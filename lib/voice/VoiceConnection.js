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
try { EventEmitter = require("eventemitter3"); } catch { EventEmitter = require("events").EventEmitter; }

let Sodium = null;
let NaCl = null;

const MAX_FRAME_SIZE = 1276 * 3;
const SILENCE_FRAME = Buffer.from([0xF8, 0xFF, 0xFE]);

const PREFERRED_MODES = [
  "aead_xchacha20_poly1305_rtpsize",
  "xsalsa20_poly1305"
];

function hasSodiumAEAD() {
  return Boolean(
    Sodium &&
    Sodium.crypto_aead_xchacha20poly1305_ietf_encrypt &&
    Sodium.crypto_aead_xchacha20poly1305_ietf_decrypt
  );
}

function pickMode(serverModes) {
  const modes = Array.isArray(serverModes) ? serverModes : [];
  for (const m of PREFERRED_MODES) {
    if (m === "aead_xchacha20_poly1305_rtpsize" && !hasSodiumAEAD()) continue;
    if (modes.includes(m)) return m;
  }
  return modes[0] || null;
}

const converterCommand = { cmd: null, libopus: false };
converterCommand.pickCommand = function () {
  let tenative;
  for (const command of ["./ffmpeg", "./avconv", "ffmpeg", "avconv"]) {
    const res = ChildProcess.spawnSync(command, ["-encoders"]);
    if (!res.error) {
      if (!res.stdout.toString().includes("libopus")) {
        tenative = command;
        continue;
      }
      converterCommand.cmd = command;
      converterCommand.libopus = true;
      return;
    }
  }
  if (tenative) converterCommand.cmd = tenative;
};

class VoiceConnection extends EventEmitter {
  constructor(id, options = {}) {
    super();
    if (typeof window !== "undefined") throw new Error("Voice is not supported in browsers");

    if (!Sodium && !NaCl) {
      try { Sodium = require("sodium-native"); }
      catch {
        try { NaCl = require("tweetnacl"); }
        catch { throw new Error("No sodium/tweetnacl"); }
      }
    }

    this.id = id;
    this.samplingRate = 48000;
    this.channels = 2;
    this.frameDuration = 20;
    this.frameSize = this.samplingRate * this.frameDuration / 1000;
    this.pcmSize = this.frameSize * this.channels * 2;
    this.bitrate = 64000;

    this.shared = !!options.shared;
    this.shard = options.shard || {};
    this.opusOnly = !!options.opusOnly;
    if (!this.opusOnly && !this.shared) this.opus = {};

    this.channelID = null;
    this.paused = true;
    this.speaking = false;
    this.sequence = 0;
    this.timestamp = 0;
    this.ssrcUserMap = {};

    this.connecting = false;
    this.reconnecting = false;
    this.resuming = false;
    this.ready = false;

    this.sendBuffer = Buffer.allocUnsafe(16 + 32 + MAX_FRAME_SIZE);
    this.sendNonce = Buffer.alloc(24);
    this.sendNonce[0] = 0x80;
    this.sendNonce[1] = 0x78;

    this.selectedMode = null;
    this.mode = null;

    if (!options.shared) {
      if (!converterCommand.cmd) converterCommand.pickCommand();
      this.piper = new Piper(converterCommand.cmd, () =>
        createOpus(this.samplingRate, this.channels, this.bitrate)
      );
    }

    this._send = this._send.bind(this);
  }

  connect(data) {
    this.connecting = true;
    if (!data.endpoint || !data.token || !data.session_id || !data.user_id) return;

    this.channelID = data.channel_id;
    this.endpoint = new URL(`wss://${data.endpoint}`);
    this.endpoint.searchParams.set("v", 4);

    this.ws = new WebSocket(this.endpoint.href);

    this.ws.on("open", () => {
      this.sendWS(
        this.resuming ? VoiceOPCodes.RESUME : VoiceOPCodes.IDENTIFY,
        {
          server_id: this.id,
          user_id: data.user_id,
          session_id: data.session_id,
          token: data.token
        }
      );
    });

    this.ws.on("message", (m) => {
      const packet = JSON.parse(m);
      switch (packet.op) {
        case VoiceOPCodes.READY: {
          this.ssrc = packet.d.ssrc;
          this.sendNonce.writeUInt32BE(this.ssrc, 8);
          const chosen = pickMode(packet.d.modes);
          if (!chosen) {
            this.disconnect(new Error("No supported voice mode"));
            return;
          }
          this.selectedMode = chosen;
          this.udpIP = packet.d.ip;
          this.udpPort = packet.d.port;
          this.udpSocket = Dgram.createSocket(Net.isIPv6(this.udpIP) ? "udp6" : "udp4");
          const msg = Buffer.allocUnsafe(74);
          msg.writeUInt32BE(this.ssrc, 4);
          this.udpSocket.send(msg, 0, msg.length, this.udpPort, this.udpIP);
          break;
        }

        case VoiceOPCodes.SESSION_DESCRIPTION:
          this.mode = packet.d.mode;
          this.secret = Buffer.from(packet.d.secret_key);
          this.ready = true;
          this.resume();
          break;

        case VoiceOPCodes.HELLO:
          this.heartbeatInterval = setInterval(() => this.heartbeat(), packet.d.heartbeat_interval);
          this.heartbeat();
          break;
      }
    });
  }

  heartbeat() {
    this.sendWS(VoiceOPCodes.HEARTBEAT, Date.now());
  }

  sendWS(op, data) {
    if (this.ws?.readyState === WebSocket.OPEN) {
      this.ws.send(JSON.stringify({ op, d: data }));
    }
  }

  resume() {
    this.paused = false;
    this.setSpeaking(1);
    this._send();
  }

  setSpeaking(v) {
    this.sendWS(VoiceOPCodes.SPEAKING, { speaking: v, delay: 0, ssrc: this.ssrc });
  }

  _send() {
    if (!this.piper) return;
    const buf = this.piper.getDataPacket();
    if (!buf) return;
    this.timestamp += this.frameSize;
    this.sequence++;
    this.sendUDPPacket(buf);
    setTimeout(this._send, this.frameDuration);
  }

  sendUDPPacket(packet) {
    if (this.udpSocket)
      this.udpSocket.send(packet, 0, packet.length, this.udpPort, this.udpIP);
  }

  disconnect(err) {
    this.ready = false;
    this.connecting = false;
    if (this.ws) this.ws.close();
    if (this.udpSocket) this.udpSocket.close();
    if (err) this.emit("error", err);
  }
}

module.exports = VoiceConnection;
