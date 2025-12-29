"use strict";

const util = require("util");
const Base = require("../structures/Base");
const ChildProcess = require("child_process");
const { VoiceOPCodes, GatewayOPCodes } = require("../Constants");
const Dgram = require("dgram");
const Net = require("net");
const Piper = require("./Piper");
const VoiceDataStream = require("./VoiceDataStream");
const { createOpus } = require("../util/Opus");

const WebSocket = typeof window !== "undefined" ? require("../util/BrowserWebSocket") : require("ws");

let EventEmitter;
try {
  EventEmitter = require("eventemitter3");
} catch {
  EventEmitter = require("events").EventEmitter;
}

let Sodium = null;
let NaCl = null;

const MAX_FRAME_SIZE = 1276 * 3;
const SILENCE_FRAME = Buffer.from([0xF8, 0xFF, 0xFE]);

const converterCommand = {
  cmd: null,
  libopus: false,
};

converterCommand.pickCommand = function pickCommand() {
  let tentative;
  for (const command of ["./ffmpeg", "./avconv", "ffmpeg", "avconv"]) {
    const res = ChildProcess.spawnSync(command, ["-encoders"]);
    if (!res.error) {
      if (!res.stdout.toString().includes("libopus")) {
        tentative = command;
        continue;
      }
      converterCommand.cmd = command;
      converterCommand.libopus = true;
      return;
    }
  }
  if (tentative) {
    converterCommand.cmd = tentative;
    return;
  }
};

function getRtpHeaderSize(buf) {
  const cc = buf[0] & 0x0f;
  const hasExtension = (buf[0] & 0x10) !== 0;
  let headerSize = 12 + cc * 4;
  if (hasExtension) {
    if (buf.length < headerSize + 4) return headerSize;
    const extLen = (buf[headerSize + 2] << 8) | buf[headerSize + 3];
    headerSize += 4 + extLen * 4;
  }
  return headerSize;
}

function hasSodiumAEAD(S) {
  return Boolean(
    S &&
      typeof S.crypto_aead_xchacha20poly1305_ietf_encrypt === "function" &&
      typeof S.crypto_aead_xchacha20poly1305_ietf_decrypt === "function" &&
      typeof S.crypto_aead_xchacha20poly1305_ietf_ABYTES === "number"
  );
}

function hasSodiumAESGCM(S) {
  return Boolean(
    S &&
      typeof S.crypto_aead_aes256gcm_encrypt === "function" &&
      typeof S.crypto_aead_aes256gcm_decrypt === "function" &&
      typeof S.crypto_aead_aes256gcm_ABYTES === "number" &&
      typeof S.crypto_aead_aes256gcm_is_available === "function" &&
      S.crypto_aead_aes256gcm_is_available()
  );
}

function pickEncryptionMode(modes, sodiumAvailable, aesGcmAvailable) {
  const list = Array.isArray(modes) ? modes : [];
  if (sodiumAvailable) {
    if (aesGcmAvailable && list.includes("aead_aes256_gcm_rtpsize")) return "aead_aes256_gcm_rtpsize";
    if (list.includes("aead_xchacha20_poly1305_rtpsize")) return "aead_xchacha20_poly1305_rtpsize";
  }
  if (list.includes("xsalsa20_poly1305_lite_rtpsize")) return "xsalsa20_poly1305_lite_rtpsize";
  if (list.includes("xsalsa20_poly1305")) return "xsalsa20_poly1305";
  if (list.includes("xsalsa20_poly1305_suffix")) return "xsalsa20_poly1305_suffix";
  if (list.includes("xsalsa20_poly1305_lite")) return "xsalsa20_poly1305_lite";
  return null;
}

class VoiceConnection extends EventEmitter {
  constructor(id, options = {}) {
    super();

    if (typeof window !== "undefined") {
      throw new Error("Voice is not supported in browsers at this time");
    }

    if (!Sodium && !NaCl) {
      try {
        Sodium = require("sodium-native");
      } catch {
        try {
          NaCl = require("tweetnacl");
        } catch {
          throw new Error("Error loading tweetnacl/libsodium, voice not available");
        }
      }
    }

    this.id = id;
    this.samplingRate = 48000;
    this.channels = 2;
    this.frameDuration = 20;
    this.frameSize = (this.samplingRate * this.frameDuration) / 1000;
    this.pcmSize = this.frameSize * this.channels * 2;
    this.bitrate = 64000;
    this.shared = !!options.shared;
    this.shard = options.shard || {};
    this.opusOnly = !!options.opusOnly;

    if (!this.opusOnly && !this.shared) {
      this.opus = {};
    }

    this.channelID = null;
    this.paused = true;
    this.speaking = false;
    this.sequence = 0;
    this.timestamp = 0;
    this.ssrcUserMap = {};
    this.connectionTimeout = null;
    this.connecting = false;
    this.reconnecting = false;
    this.resuming = false;
    this.ready = false;

    this.sendBuffer = Buffer.allocUnsafe(16 + 32 + MAX_FRAME_SIZE);

    this.sendNonce = Buffer.alloc(24);
    this.sendNonce[0] = 0x80;
    this.sendNonce[1] = 0x78;

    this.rtpHeader = Buffer.allocUnsafe(12);
    this.rtpHeader[0] = 0x80;
    this.rtpHeader[1] = 0x78;

    this.encryptionMode = null;
    this.nonceCounter = 0;

    if (!options.shared) {
      if (!converterCommand.cmd) {
        converterCommand.pickCommand();
      }

      this.piper = new Piper(converterCommand.cmd, () => createOpus(this.samplingRate, this.channels, this.bitrate));
      this.piper.on("error", (e) => this.emit("error", e));
      if (!converterCommand.libopus) {
        this.piper.libopus = false;
      }
    }

    this._send = this._send.bind(this);
  }

  get volume() {
    return this.piper.volumeLevel;
  }

  connect(data) {
    this.connecting = true;
    if (this.ws && this.ws.readyState !== WebSocket.CLOSED) {
      this.disconnect(undefined, true);
      setTimeout(() => {
        if (!this.connecting && !this.ready) {
          this.connect(data);
        }
      }, 500).unref();
      return;
    }
    clearTimeout(this.connectionTimeout);
    this.connectionTimeout = setTimeout(() => {
      if (this.connecting) {
        this.disconnect(new Error("Voice connection timeout"));
      }
      this.connectionTimeout = null;
    }, this.shard.client ? this.shard.client.options.connectionTimeout : 30000).unref();
    if (!data.endpoint) {
      return;
    }
    if (!data.token || !data.session_id || !data.user_id) {
      this.disconnect(new Error("Malformed voice server update: " + JSON.stringify(data)));
      return;
    }
    this.channelID = data.channel_id;
    this.endpoint = new URL(`wss://${data.endpoint}`);
    if (this.endpoint.port === "80") {
      this.endpoint.port = "";
    }
    this.endpoint.searchParams.set("v", 4);
    this.ws = new WebSocket(this.endpoint.href);
    this.emit("debug", "Connection: " + JSON.stringify(data));
    this.ws.on("open", () => {
      this.emit("connect");
      if (this.connectionTimeout) {
        clearTimeout(this.connectionTimeout);
        this.connectionTimeout = null;
      }
      if (this.resuming) {
        this.sendWS(VoiceOPCodes.RESUME, {
          server_id: this.id,
          session_id: data.session_id,
          token: data.token,
        });
      } else {
        this.sendWS(VoiceOPCodes.IDENTIFY, {
          server_id: this.id,
          user_id: data.user_id,
          session_id: data.session_id,
          token: data.token,
        });
      }
    });
    this.ws.on("message", (m) => {
      const packet = JSON.parse(m);
      if (this.listeners("debug").length > 0) {
        this.emit("debug", "Rec: " + JSON.stringify(packet));
      }
      switch (packet.op) {
        case VoiceOPCodes.READY: {
          this.ssrc = packet.d.ssrc;
          this.sendNonce.writeUInt32BE(this.ssrc, 8);
          this.rtpHeader.writeUInt32BE(this.ssrc, 8);

          const sodiumAEAD = hasSodiumAEAD(Sodium);
          const sodiumAES = hasSodiumAESGCM(Sodium);
          const chosen = pickEncryptionMode(packet.d.modes, sodiumAEAD, sodiumAES);

          if (!chosen) {
            throw new Error("No supported voice mode found");
          }

          this.encryptionMode = chosen;
          this.modes = packet.d.modes;

          this.udpIP = packet.d.ip;
          this.udpPort = packet.d.port;

          this.emit("debug", "Connecting to UDP: " + this.udpIP + ":" + this.udpPort);

          this.udpSocket = Dgram.createSocket(Net.isIPv6(this.udpIP) ? "udp6" : "udp4");
          this.udpSocket.on("error", (err, msg) => {
            this.emit("error", err);
            if (msg) {
              this.emit("debug", "Voice UDP error: " + msg);
            }
            if (this.ready || this.connecting) {
              this.disconnect(err);
            }
          });
          this.udpSocket.once("message", (packet2) => {
            let i = 8;
            while (packet2[i] !== 0) {
              i++;
            }
            const localIP = packet2.toString("ascii", 8, i);
            const localPort = packet2.readUInt16BE(packet2.length - 2);
            this.emit("debug", `Discovered IP: ${localIP}:${localPort} (${packet2.toString("hex")})`);

            this.sendWS(VoiceOPCodes.SELECT_PROTOCOL, {
              protocol: "udp",
              data: {
                address: localIP,
                port: localPort,
                mode: this.encryptionMode,
              },
            });
          });
          this.udpSocket.on("close", (err) => {
            if (err) {
              this.emit("warn", "Voice UDP close: " + err);
            }
            if (this.ready || this.connecting) {
              this.disconnect(err);
            }
          });
          const udpMessage = Buffer.allocUnsafe(74);
          udpMessage.writeUInt16BE(0x1, 0);
          udpMessage.writeUInt16BE(70, 2);
          udpMessage.writeUInt32BE(this.ssrc, 4);
          this.sendUDPPacket(udpMessage);
          break;
        }
        case VoiceOPCodes.RESUMED: {
          this.connecting = false;
          this.resuming = false;
          break;
        }
        case VoiceOPCodes.SESSION_DESCRIPTION: {
          this.mode = packet.d.mode;
          if (!this.encryptionMode) this.encryptionMode = this.mode;
          this.secret = Buffer.from(packet.d.secret_key);
          this.connecting = false;
          this.reconnecting = false;
          this.ready = true;
          this.sendAudioFrame(SILENCE_FRAME, this.frameSize);
          this.emit("ready");
          this.resume();
          if (this.receiveStreamOpus || this.receiveStreamPCM) {
            this.registerReceiveEventHandler();
          }
          break;
        }
        case VoiceOPCodes.HEARTBEAT_ACK: {
          this.emit("pong", Date.now() - packet.d);
          break;
        }
        case VoiceOPCodes.SPEAKING: {
          this.ssrcUserMap[packet.d.ssrc] = packet.d.user_id;
          this.emit(packet.d.speaking ? "speakingStart" : "speakingStop", packet.d.user_id);
          break;
        }
        case VoiceOPCodes.HELLO: {
          if (this.heartbeatInterval) {
            clearInterval(this.heartbeatInterval);
          }
          this.heartbeatInterval = setInterval(() => {
            this.heartbeat();
          }, packet.d.heartbeat_interval);

          this.heartbeat();
          break;
        }
        case VoiceOPCodes.CLIENTS_CONNECT: {
          this.emit("usersConnect", packet.d.user_ids);
          break;
        }
        case VoiceOPCodes.CLIENT_DISCONNECT: {
          if (this.opus) {
            if (this.opus[packet.d.user_id] && this.opus[packet.d.user_id].delete) {
              this.opus[packet.d.user_id].delete();
            }
            delete this.opus[packet.d.user_id];
          }
          this.emit("userDisconnect", packet.d.user_id);
          break;
        }
        default: {
          this.emit("unknown", packet);
          break;
        }
      }
    });
    this.ws.on("error", (err) => {
      this.emit("error", err);
    });
    this.ws.on("close", (code, reason) => {
      let err = !code || code === 1000 ? null : new Error(code + ": " + reason);
      this.emit("warn", `Voice WS close ${code}: ${reason}`);
      if (this.connecting || this.ready) {
        let reconnecting = true;
        if (code < 4000 || code === 4015) {
          this.resuming = true;
          setTimeout(() => {
            this.connect(data);
          }, 500).unref();
          return;
        }
        if (code === 4006) {
          reconnecting = false;
        } else if (code === 4014) {
          if (this.channelID) {
            data.endpoint = null;
            reconnecting = true;
            err = null;
          } else {
            reconnecting = false;
          }
        } else if (code === 1000) {
          reconnecting = false;
        }
        this.disconnect(err, reconnecting);
        if (reconnecting) {
          setTimeout(() => {
            if (!this.connecting && !this.ready) {
              this.connect(data);
            }
          }, 500).unref();
        }
      }
    });
  }

  disconnect(error, reconnecting) {
    this.connecting = false;
    this.reconnecting = reconnecting;
    this.resuming = false;
    this.ready = false;
    this.speaking = false;
    this.timestamp = 0;
    this.sequence = 0;

    if (this.connectionTimeout) {
      clearTimeout(this.connectionTimeout);
      this.connectionTimeout = null;
    }

    try {
      if (reconnecting) {
        this.pause();
      } else {
        this.stopPlaying();
      }
    } catch (err) {
      this.emit("error", err);
    }
    if (this.heartbeatInterval) {
      clearInterval(this.heartbeatInterval);
      this.heartbeatInterval = null;
    }
    if (this.udpSocket) {
      try {
        this.udpSocket.close();
      } catch (err) {
        if (err.message !== "Not running") {
          this.emit("error", err);
        }
      }
      this.udpSocket = null;
    }
    if (this.ws) {
      try {
        if (reconnecting) {
          if (this.ws.readyState === WebSocket.OPEN) {
            this.ws.close(4901, "Eris: reconnect");
          } else {
            this.emit("debug", `Terminating websocket (state: ${this.ws.readyState})`);
            this.ws.terminate();
          }
        } else {
          this.ws.close(1000, "Eris: normal");
        }
      } catch (err) {
        this.emit("error", err);
      }
      this.ws = null;
    }
    if (reconnecting) {
      if (error) {
        this.emit("error", error);
      }
    } else {
      this.channelID = null;
      this.updateVoiceState();
      this.emit("disconnect", error);
    }
  }

  heartbeat() {
    this.sendWS(VoiceOPCodes.HEARTBEAT, Date.now());
    if (this.udpSocket) {
      const udpMessage = Buffer.from([0x80, 0xC8, 0x0, 0x0]);
      this.sendUDPPacket(udpMessage);
    }
  }

  pause() {
    this.paused = true;
    this.setSpeaking(0);
    if (this.current) {
      if (!this.current.pausedTimestamp) {
        this.current.pausedTimestamp = Date.now();
      }
      if (this.current.timeout) {
        clearTimeout(this.current.timeout);
        this.current.timeout = null;
      }
    }
  }

  play(source, options = {}) {
    if (this.shared) {
      throw new Error("Cannot play stream on shared voice connection");
    }
    if (!this.ready) {
      throw new Error("Not ready yet");
    }

    options.format = options.format || null;
    options.voiceDataTimeout = !isNaN(options.voiceDataTimeout) ? options.voiceDataTimeout : 2000;
    options.inlineVolume = !!options.inlineVolume;
    options.inputArgs = options.inputArgs || [];
    options.encoderArgs = options.encoderArgs || [];

    options.samplingRate = options.samplingRate || this.samplingRate;
    options.frameDuration = options.frameDuration || this.frameDuration;
    options.frameSize = options.frameSize || (options.samplingRate * options.frameDuration) / 1000;
    options.pcmSize = options.pcmSize || options.frameSize * 2 * this.channels;

    if (!this.piper.encode(source, options)) {
      this.emit("error", new Error("Unable to encode source"));
      return;
    }

    this.ended = false;
    this.current = {
      startTime: 0,
      playTime: 0,
      pausedTimestamp: 0,
      pausedTime: 0,
      bufferingTicks: 0,
      options: options,
      timeout: null,
      buffer: null,
    };

    this.playing = true;
    this.emit("start");
    this._send();
  }

  receive(type) {
    if (type === "pcm") {
      if (!this.receiveStreamPCM) {
        this.receiveStreamPCM = new VoiceDataStream(type);
        if (!this.receiveStreamOpus) {
          this.registerReceiveEventHandler();
        }
      }
    } else if (type === "opus") {
      if (!this.receiveStreamOpus) {
        this.receiveStreamOpus = new VoiceDataStream(type);
        if (!this.receiveStreamPCM) {
          this.registerReceiveEventHandler();
        }
      }
    } else {
      throw new Error(`Unsupported voice data type: ${type}`);
    }
    return type === "pcm" ? this.receiveStreamPCM : this.receiveStreamOpus;
  }

  registerReceiveEventHandler() {
    this.udpSocket.on("message", (msg) => {
      if (msg[1] !== 0x78) {
        return;
      }

      const mode = this.mode || this.encryptionMode;

      let headerSize = 12;
      if (mode && mode.endsWith("_rtpsize")) {
        headerSize = getRtpHeaderSize(msg);
        if (headerSize < 12) headerSize = 12;
      }

      const rtpHeader = msg.subarray(0, headerSize);

      let userID = null;
      let ts = 0;
      let seq = 0;

      if (rtpHeader.length >= 12) {
        const ssrc = rtpHeader.readUInt32BE(8);
        userID = this.ssrcUserMap[ssrc] || null;
        seq = rtpHeader.readUInt16BE(2);
        ts = rtpHeader.readUInt32BE(4);
      }

      let data;

      if (mode === "aead_xchacha20_poly1305_rtpsize") {
        if (!Sodium || !hasSodiumAEAD(Sodium)) {
          this.emit("warn", "AEAD XChaCha20 required but libsodium-native not available");
          return;
        }
        if (msg.length < headerSize + 16 + 4) return;
        const counter = msg.readUInt32LE(msg.length - 4);
        const nonce = Buffer.alloc(24);
        nonce.writeUInt32LE(counter >>> 0, 0);
        const cipher = msg.subarray(headerSize, msg.length - 4);
        const plain = Buffer.alloc(cipher.length - Sodium.crypto_aead_xchacha20poly1305_ietf_ABYTES);
        try {
          const ok = Sodium.crypto_aead_xchacha20poly1305_ietf_decrypt(plain, null, cipher, rtpHeader, nonce, this.secret);
          if (!ok) {
            this.emit("warn", "Failed to decrypt received packet");
            return;
          }
          data = plain;
        } catch {
          this.emit("warn", "Failed to decrypt received packet");
          return;
        }
      } else if (mode === "aead_aes256_gcm_rtpsize") {
        if (!Sodium || !hasSodiumAESGCM(Sodium)) {
          this.emit("warn", "AEAD AES256-GCM required but not available");
          return;
        }
        if (msg.length < headerSize + 16 + 4) return;
        const counter = msg.readUInt32LE(msg.length - 4);
        const nonce = Buffer.alloc(12);
        nonce.writeUInt32LE(counter >>> 0, 0);
        const cipher = msg.subarray(headerSize, msg.length - 4);
        const plain = Buffer.alloc(cipher.length - Sodium.crypto_aead_aes256gcm_ABYTES);
        try {
          const ok = Sodium.crypto_aead_aes256gcm_decrypt(plain, null, cipher, rtpHeader, nonce, this.secret);
          if (!ok) {
            this.emit("warn", "Failed to decrypt received packet");
            return;
          }
          data = plain;
        } catch {
          this.emit("warn", "Failed to decrypt received packet");
          return;
        }
      } else if (mode === "xsalsa20_poly1305_lite_rtpsize" || mode === "xsalsa20_poly1305_lite") {
        if (!Sodium && !NaCl) return;
        if (msg.length < headerSize + 16 + 4) return;
        const counter = msg.readUInt32LE(msg.length - 4);
        const nonce = Buffer.alloc(24);
        nonce.writeUInt32LE(counter >>> 0, 0);
        const cipher = msg.subarray(headerSize, msg.length - 4);
        if (Sodium) {
          data = Buffer.alloc(cipher.length - Sodium.crypto_secretbox_MACBYTES);
          try {
            const ok = Sodium.crypto_secretbox_open_easy(data, cipher, nonce, this.secret);
            if (!ok) {
              this.emit("warn", "Failed to decrypt received packet");
              return;
            }
          } catch {
            this.emit("warn", "Failed to decrypt received packet");
            return;
          }
        } else {
          const opened = NaCl.secretbox.open(cipher, nonce, this.secret);
          if (!opened) {
            this.emit("warn", "Failed to decrypt received packet");
            return;
          }
          data = Buffer.from(opened);
        }
      } else if (mode === "xsalsa20_poly1305_suffix") {
        if (!Sodium && !NaCl) return;
        if (msg.length < headerSize + 16 + 24) return;
        const nonce = msg.subarray(msg.length - 24);
        const cipher = msg.subarray(headerSize, msg.length - 24);
        if (Sodium) {
          data = Buffer.alloc(cipher.length - Sodium.crypto_secretbox_MACBYTES);
          try {
            const ok = Sodium.crypto_secretbox_open_easy(data, cipher, nonce, this.secret);
            if (!ok) {
              this.emit("warn", "Failed to decrypt received packet");
              return;
            }
          } catch {
            this.emit("warn", "Failed to decrypt received packet");
            return;
          }
        } else {
          const opened = NaCl.secretbox.open(cipher, nonce, this.secret);
          if (!opened) {
            this.emit("warn", "Failed to decrypt received packet");
            return;
          }
          data = Buffer.from(opened);
        }
      } else {
        if (!Sodium && !NaCl) return;
        const nonce = Buffer.alloc(24);
        msg.copy(nonce, 0, 0, 12);
        const cipher = msg.subarray(12);
        if (Sodium) {
          data = Buffer.alloc(cipher.length - Sodium.crypto_secretbox_MACBYTES);
          try {
            const ok = Sodium.crypto_secretbox_open_easy(data, cipher, nonce, this.secret);
            if (!ok) {
              this.emit("warn", "Failed to decrypt received packet");
              return;
            }
          } catch {
            this.emit("warn", "Failed to decrypt received packet");
            return;
          }
        } else {
          const opened = NaCl.secretbox.open(cipher, nonce, this.secret);
          if (!opened) {
            this.emit("warn", "Failed to decrypt received packet");
            return;
          }
          data = Buffer.from(opened);
        }
      }

      if (!data) return;

      const hasExtension = !!(rtpHeader[0] & 0b10000);
      const cc = rtpHeader[0] & 0b1111;

      if (!(mode && mode.endsWith("_rtpsize"))) {
        if (cc > 0) {
          data = data.subarray(cc * 4);
        }
        if (hasExtension) {
          const l = (data[2] << 8) | data[3];
          data = data.subarray(4 + l * 4);
        }
      }

      if (this.receiveStreamOpus) {
        this.receiveStreamOpus.emit("data", data, userID, ts, seq);
      }

      if (this.receiveStreamPCM) {
        if (!userID) return;
        if (!this.opus[userID]) {
          this.opus[userID] = createOpus(this.samplingRate, this.channels, this.bitrate);
        }
        const decoded = this.opus[userID].decode(data, this.frameSize);
        if (!decoded) {
          return this.emit("warn", "Failed to decode received packet");
        }
        this.receiveStreamPCM.emit("data", decoded, userID, ts, seq);
      }
    });
  }

  resume() {
    this.paused = false;
    if (this.current) {
      this.setSpeaking(1);
      if (this.current.pausedTimestamp) {
        this.current.pausedTime += Date.now() - this.current.pausedTimestamp;
        this.current.pausedTimestamp = 0;
      }
      this._send();
    } else {
      this.setSpeaking(0);
    }
  }

  sendAudioFrame(frame, frameSize = this.frameSize) {
    this.timestamp = (this.timestamp + frameSize) >>> 0;
    this.sequence = (this.sequence + 1) & 0xffff;
    return this._sendAudioFrame(frame);
  }

  sendUDPPacket(packet) {
    if (this.udpSocket) {
      try {
        this.udpSocket.send(packet, 0, packet.length, this.udpPort, this.udpIP);
      } catch (e) {
        this.emit("error", e);
      }
    }
  }

  sendWS(op, data) {
    if (this.ws && this.ws.readyState === WebSocket.OPEN) {
      data = JSON.stringify({ op: op, d: data });
      this.ws.send(data);
      this.emit("debug", data);
    }
  }

  setSpeaking(value, delay = 0) {
    this.speaking = value === true ? 1 : value === false ? 0 : value;
    this.sendWS(VoiceOPCodes.SPEAKING, {
      speaking: value,
      delay: delay,
      ssrc: this.ssrc,
    });
  }

  setVolume(volume) {
    this.piper.setVolume(volume);
  }

  stopPlaying() {
    if (this.ended) {
      return;
    }
    this.ended = true;
    if (this.current && this.current.timeout) {
      clearTimeout(this.current.timeout);
      this.current.timeout = null;
    }
    this.current = null;
    if (this.piper) {
      this.piper.stop();
      this.piper.resetPackets();
    }

    if (this.secret) {
      for (let i = 0; i < 5; i++) {
        this.sendAudioFrame(SILENCE_FRAME, this.frameSize);
      }
    }
    this.playing = false;
    this.setSpeaking(0);
    this.emit("end");
  }

  switchChannel(channelID, reactive) {
    if (this.channelID === channelID) {
      return;
    }

    this.channelID = channelID;
    if (reactive) {
      if (this.reconnecting && !channelID) {
        this.disconnect();
      }
    } else {
      this.updateVoiceState();
    }
  }

  updateVoiceState(selfMute, selfDeaf) {
    if (this.shard.sendWS) {
      this.shard.sendWS(GatewayOPCodes.VOICE_STATE_UPDATE, {
        guild_id: this.id === "call" ? null : this.id,
        channel_id: this.channelID || null,
        self_mute: !!selfMute,
        self_deaf: !!selfDeaf,
      });
    }
  }

  _destroy() {
    if (this.opus) {
      for (const key in this.opus) {
        if (this.opus[key].delete) {
          this.opus[key].delete();
        }
        delete this.opus[key];
      }
    }
    delete this.piper;
    if (this.receiveStreamOpus) {
      this.receiveStreamOpus.removeAllListeners();
      this.receiveStreamOpus = null;
    }
    if (this.receiveStreamPCM) {
      this.receiveStreamPCM.removeAllListeners();
      this.receiveStreamPCM = null;
    }
  }

  _send() {
    if (!this.piper.encoding && this.piper.dataPacketCount === 0) {
      return this.stopPlaying();
    }

    if ((this.current.buffer = this.piper.getDataPacket())) {
      if (this.current.startTime === 0) {
        this.current.startTime = Date.now();
      }
      if (this.current.bufferingTicks > 0) {
        this.current.bufferingTicks = 0;
        this.setSpeaking(1);
      }
    } else if (
      this.current.options.voiceDataTimeout === -1 ||
      this.current.bufferingTicks < this.current.options.voiceDataTimeout / (4 * this.current.options.frameDuration)
    ) {
      if (++this.current.bufferingTicks === 1) {
        this.setSpeaking(0);
      }
      this.current.pausedTime += 4 * this.current.options.frameDuration;
      this.timestamp = (this.timestamp + 3 * this.current.options.frameSize) >>> 0;
      this.current.timeout = setTimeout(this._send, 4 * this.current.options.frameDuration);
      return;
    } else {
      return this.stopPlaying();
    }

    this.sendAudioFrame(this.current.buffer, this.current.options.frameSize);
    this.current.playTime += this.current.options.frameDuration;
    this.current.timeout = setTimeout(this._send, this.current.startTime + this.current.pausedTime + this.current.playTime - Date.now());
  }

  _sendAudioFrame(frame) {
    const mode = this.mode || this.encryptionMode;

    if (mode === "aead_xchacha20_poly1305_rtpsize") {
      if (!Sodium || !hasSodiumAEAD(Sodium)) {
        throw new Error("AEAD XChaCha20 required but libsodium-native not available");
      }

      this.rtpHeader.writeUInt16BE(this.sequence, 2);
      this.rtpHeader.writeUInt32BE(this.timestamp, 4);

      const nonceCounter = (this.nonceCounter = (this.nonceCounter + 1) >>> 0);
      const nonce = Buffer.alloc(24);
      nonce.writeUInt32LE(nonceCounter, 0);

      const ad = this.rtpHeader;
      const out = Buffer.alloc(frame.length + Sodium.crypto_aead_xchacha20poly1305_ietf_ABYTES);
      Sodium.crypto_aead_xchacha20poly1305_ietf_encrypt(out, frame, ad, null, nonce, this.secret);

      const packet = Buffer.allocUnsafe(this.rtpHeader.length + out.length + 4);
      this.rtpHeader.copy(packet, 0);
      out.copy(packet, this.rtpHeader.length);
      packet.writeUInt32LE(nonceCounter, packet.length - 4);

      return this.sendUDPPacket(packet);
    }

    if (mode === "aead_aes256_gcm_rtpsize") {
      if (!Sodium || !hasSodiumAESGCM(Sodium)) {
        throw new Error("AEAD AES256-GCM required but not available");
      }

      this.rtpHeader.writeUInt16BE(this.sequence, 2);
      this.rtpHeader.writeUInt32BE(this.timestamp, 4);

      const nonceCounter = (this.nonceCounter = (this.nonceCounter + 1) >>> 0);
      const nonce = Buffer.alloc(12);
      nonce.writeUInt32LE(nonceCounter, 0);

      const ad = this.rtpHeader;
      const out = Buffer.alloc(frame.length + Sodium.crypto_aead_aes256gcm_ABYTES);
      Sodium.crypto_aead_aes256gcm_encrypt(out, frame, ad, null, nonce, this.secret);

      const packet = Buffer.allocUnsafe(this.rtpHeader.length + out.length + 4);
      this.rtpHeader.copy(packet, 0);
      out.copy(packet, this.rtpHeader.length);
      packet.writeUInt32LE(nonceCounter, packet.length - 4);

      return this.sendUDPPacket(packet);
    }

    if (mode === "xsalsa20_poly1305_lite_rtpsize" || mode === "xsalsa20_poly1305_lite") {
      const nonceCounter = (this.nonceCounter = (this.nonceCounter + 1) >>> 0);
      const nonce = Buffer.alloc(24);
      nonce.writeUInt32LE(nonceCounter, 0);

      this.rtpHeader.writeUInt16BE(this.sequence, 2);
      this.rtpHeader.writeUInt32BE(this.timestamp, 4);

      if (Sodium) {
        const MACBYTES = Sodium.crypto_secretbox_MACBYTES;
        const out = Buffer.alloc(frame.length + MACBYTES);
        Sodium.crypto_secretbox_easy(out, frame, nonce, this.secret);
        const packet = Buffer.allocUnsafe(this.rtpHeader.length + out.length + 4);
        this.rtpHeader.copy(packet, 0);
        out.copy(packet, this.rtpHeader.length);
        packet.writeUInt32LE(nonceCounter, packet.length - 4);
        return this.sendUDPPacket(packet);
      } else {
        const boxed = NaCl.secretbox(new Uint8Array(frame), new Uint8Array(nonce), new Uint8Array(this.secret));
        const out = Buffer.from(boxed);
        const packet = Buffer.allocUnsafe(this.rtpHeader.length + out.length + 4);
        this.rtpHeader.copy(packet, 0);
        out.copy(packet, this.rtpHeader.length);
        packet.writeUInt32LE(nonceCounter, packet.length - 4);
        return this.sendUDPPacket(packet);
      }
    }

    this.sendNonce.writeUInt16BE(this.sequence, 2);
    this.sendNonce.writeUInt32BE(this.timestamp, 4);

    if (mode === "xsalsa20_poly1305_suffix") {
      if (Sodium) {
        const nonce = Buffer.alloc(24);
        Sodium.randombytes_buf(nonce);
        const MACBYTES = Sodium.crypto_secretbox_MACBYTES;
        const out = Buffer.alloc(frame.length + MACBYTES);
        Sodium.crypto_secretbox_easy(out, frame, nonce, this.secret);
        const packet = Buffer.allocUnsafe(12 + out.length + 24);
        this.sendNonce.copy(packet, 0, 0, 12);
        out.copy(packet, 12);
        nonce.copy(packet, 12 + out.length);
        return this.sendUDPPacket(packet);
      } else {
        const nonce = Buffer.alloc(24);
        for (let i = 0; i < 24; i++) nonce[i] = (Math.random() * 256) | 0;
        const boxed = NaCl.secretbox(new Uint8Array(frame), new Uint8Array(nonce), new Uint8Array(this.secret));
        const out = Buffer.from(boxed);
        const packet = Buffer.allocUnsafe(12 + out.length + 24);
        this.sendNonce.copy(packet, 0, 0, 12);
        out.copy(packet, 12);
        nonce.copy(packet, 12 + out.length);
        return this.sendUDPPacket(packet);
      }
    }

    if (mode === "xsalsa20_poly1305_lite") {
      const nonceCounter = (this.nonceCounter = (this.nonceCounter + 1) >>> 0);
      const nonce = Buffer.alloc(24);
      nonce.writeUInt32LE(nonceCounter, 0);

      if (Sodium) {
        const MACBYTES = Sodium.crypto_secretbox_MACBYTES;
        const out = Buffer.alloc(frame.length + MACBYTES);
        Sodium.crypto_secretbox_easy(out, frame, nonce, this.secret);
        const packet = Buffer.allocUnsafe(12 + out.length + 4);
        this.sendNonce.copy(packet, 0, 0, 12);
        out.copy(packet, 12);
        packet.writeUInt32LE(nonceCounter, packet.length - 4);
        return this.sendUDPPacket(packet);
      } else {
        const boxed = NaCl.secretbox(new Uint8Array(frame), new Uint8Array(nonce), new Uint8Array(this.secret));
        const out = Buffer.from(boxed);
        const packet = Buffer.allocUnsafe(12 + out.length + 4);
        this.sendNonce.copy(packet, 0, 0, 12);
        out.copy(packet, 12);
        packet.writeUInt32LE(nonceCounter, packet.length - 4);
        return this.sendUDPPacket(packet);
      }
    }

    if (Sodium) {
      const MACBYTES = Sodium.crypto_secretbox_MACBYTES;
      const length = frame.length + MACBYTES;
      this.sendBuffer.fill(0, 12, 12 + MACBYTES);
      frame.copy(this.sendBuffer, 12 + MACBYTES);
      Sodium.crypto_secretbox_easy(
        this.sendBuffer.subarray(12, 12 + length),
        this.sendBuffer.subarray(12 + MACBYTES, 12 + length),
        this.sendNonce,
        this.secret
      );
      this.sendNonce.copy(this.sendBuffer, 0, 0, 12);
      return this.sendUDPPacket(this.sendBuffer.subarray(0, 12 + length));
    } else {
      const BOXZEROBYTES = NaCl.lowlevel.crypto_secretbox_BOXZEROBYTES;
      const ZEROBYTES = NaCl.lowlevel.crypto_secretbox_ZEROBYTES;
      const length = frame.length + BOXZEROBYTES;
      this.sendBuffer.fill(0, BOXZEROBYTES, BOXZEROBYTES + ZEROBYTES);
      frame.copy(this.sendBuffer, BOXZEROBYTES + ZEROBYTES);
      NaCl.lowlevel.crypto_secretbox(this.sendBuffer, this.sendBuffer.subarray(BOXZEROBYTES), ZEROBYTES + frame.length, this.sendNonce, this.secret);
      this.sendNonce.copy(this.sendBuffer, BOXZEROBYTES - 12, 0, 12);
      return this.sendUDPPacket(this.sendBuffer.subarray(BOXZEROBYTES - 12, BOXZEROBYTES + length));
    }
  }

  _sendAudioPacket(audio) {
    return this._sendAudioFrame(audio);
  }

  [util.inspect.custom]() {
    return Base.prototype[util.inspect.custom].call(this);
  }

  toString() {
    return `[VoiceConnection ${this.channelID}]`;
  }

  toJSON(props = []) {
    return Base.prototype.toJSON.call(this, [
      "channelID",
      "connecting",
      "current",
      "id",
      "paused",
      "playing",
      "ready",
      "volume",
      ...props,
    ]);
  }
}

VoiceConnection._converterCommand = converterCommand;

module.exports = VoiceConnection;
