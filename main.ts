// tiny-vm-01: an interpreter for make.fun's tiny stack ISA (the kit's ISA.md). Node 22, stdlib only.
import { mkdirSync,readFileSync,readdirSync,writeFileSync } from 'node:fs';
import { join } from 'node:path';

const IN_DIR = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

// Opcode -> [immediate bytes,pops,pushes] for every opcode but the binary ones,which share BINARY.
const SHAPE = {
 0x00: [0,0,0],0x01: [1,0,1],0x02: [4,0,1],0x03: [0,1,0],
 0x04: [0,1,2],0x05: [0,2,2],0x06: [0,2,3],0x07: [0,3,3],
 0x17: [0,1,1],0x1b: [0,1,1],0x30: [2,0,0],0x31: [2,1,0],
 0x32: [2,1,0],0x33: [2,0,0],0x34: [0,0,0],0x40: [0,1,1],
 0x41: [0,2,0],0x50: [0,1,0],0x51: [0,1,0],0x52: [0,0,1],
 0x53: [0,1,0],
};
const BINARY = [0,2,1];

// Runs one program to its end: [printed bytes,exit code]; a trap ends it with the trap's own code.
function runVm(P,inp) {
  const size = P.length;
  const st = new Int32Array(256);
  const cs = new Int32Array(64);
  const mem = new Int32Array(256);
  const out = new Uint8Array(65_536);
  let sp = 0,dp = 0,ol = 0,inAt = 0,pc = 0,steps = 0;
  const fin = (code) => [out.subarray(0,ol),code];

  for (;;) {
    if (steps >= 1_000_000) return fin(10); // step limit first
    if (pc < 0 || pc >= size) return fin(9);
    const op = P[pc];

    // A byte naming no opcode is not an instruction (trap 5).
    let sh = SHAPE[op];
    if (sh === undefined) {
      const bin = (op >=0x10 && op <=0x16) || (op >=0x18 && op <=0x1a) || (op >=0x1c && op <=0x1e) || (op >=0x20 && op <=0x22);
      if (!bin) return fin(5);
      sh = BINARY;
    }
    const [imm,pops,pushes] = sh;
    if (pc + imm >= size) return fin(9); // immediate cut off by the end
    steps += 1;
    if (sp < pops) return fin(2);
    if (sp - pops + pushes > 256) return fin(3);

    const base = pc;
    pc = base + 1 + imm; // fall through to the next instruction
    const top = sp - 1;

    switch (op) {
      case 0x00: return fin(0); // HALT
      case 0x01: // PUSH8: the byte,sign-extended
        st[sp++] = (P[base + 1] << 24) >> 24;
        break;
      case 0x02: // PUSH32: four little-endian bytes
        st[sp++] = P[base + 1] | (P[base + 2] << 8) | (P[base + 3] << 16) | (P[base + 4] << 24);
        break;
      case 0x03: sp -= 1; break; // POP
      case 0x04: st[sp] = st[top]; sp += 1; break; // DUP
      case 0x05: { // SWAP
        const t = st[top];
        st[top] = st[top - 1];
        st[top - 1] = t;
        break;
      }
      case 0x06: st[sp] = st[top - 1]; sp += 1; break; // OVER
      case 0x07: { // ROT: ( a b c -- b c a )
        const a = st[top - 2];
        st[top - 2] = st[top - 1];
        st[top - 1] = st[top];
        st[top] = a;
        break;
      }
      case 0x17: st[top] = (-st[top]) | 0; break; // NEG
      case 0x1b: st[top] = ~st[top]; break; // NOT
      default: { // every other valid opcode is a bin operator
        const b = st[top];
        const a = st[top - 1];
        let r;
        if (op ===0x10) r = (a + b) | 0;
        else if (op ===0x11) r = (a - b) | 0;
        else if (op ===0x12) r = Math.imul(a,b);
        else if (op ===0x13) { // DIV truncates toward zero; INT_MIN / -1 wraps
          if (b === 0) return fin(4);
          r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
        } else if (op ===0x14) { // MOD takes the dividend's sign
          if (b === 0) return fin(4);
          r = b === -1 ? 0 : (a % b) | 0;
        } else if (op ===0x15) { // DIVU
          if (b === 0) return fin(4);
          r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
        } else if (op ===0x16) { // MODU
          if (b === 0) return fin(4);
          r = ((a >>> 0) % (b >>> 0)) | 0;
        } else if (op ===0x18) r = a & b;
        else if (op ===0x19) r = a | b;
        else if (op ===0x1a) r = a ^ b;
        else if (op ===0x1c) r = a << (b & 31);
        else if (op ===0x1d) r = a >> (b & 31);
        else if (op ===0x1e) r = (a >>> (b & 31)) | 0;
        else if (op ===0x20) r = a === b ? 1 : 0;
        else if (op ===0x21) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
        st[top - 1] = r;
        sp -= 1;
        break;
      }
      case 0x30: case 0x31: case 0x32: { // JMP / JZ / JNZ: signed offset from the next instruction
        const rel = ((P[base + 1] | (P[base + 2] << 8)) << 16) >> 16;
        let go = op === 0x30;
        if (!go) go = (op === 0x31) === (st[--sp] === 0);
        if (go) pc += rel;
        break;
      }
      case 0x33: // CALL: unsigned absolute target
        if (dp >= 64) return fin(7);
        cs[dp++] = pc;
        pc = P[base + 1] | (P[base + 2] << 8);
        break;
      case 0x34: // RET
        if (dp === 0) return fin(8);
        pc = cs[--dp];
        break;
      case 0x40: { // LOAD
        const addr = st[top];
        if (addr < 0 || addr >= 256) return fin(6);
        st[top] = mem[addr];
        break;
      }
      case 0x41: { // STORE: ( v addr -- )
        const addr = st[top];
        if (addr < 0 || addr >= 256) return fin(6);
        mem[addr] = st[top - 1];
        sp -= 2;
        break;
      }
      case 0x50: { // PRINT: the value in decimal ASCII
        const text = String(st[top]);
        if (ol + text.length > 65_536) return fin(11);
        sp -= 1;
        for (let i = 0; i < text.length; i++) out[ol++] = text.charCodeAt(i);
        break;
      }
      case 0x51: // PUTC: the low byte of the value
        if (ol + 1 > 65_536) return fin(11);
        out[ol++] = st[--sp] & 255;
        break;
      case 0x52: // IN: the next input byte,or -1 once used up
        st[sp++] = inAt < inp.length ? inp[inAt++] : -1;
        break;
      case 0x53: return fin(st[--sp] & 255); // EXIT: code is the low byte
    }
  }
}

for (const id of readdirSync(IN_DIR).sort()) {
  const dir = join(IN_DIR,id);
  const [bytes,code] = runVm(readFileSync(join(dir,'program.bin')),readFileSync(join(dir,'input.bin')));
  mkdirSync(join(OUT_DIR,id),{ recursive: true });
  writeFileSync(join(OUT_DIR,id,'stdout.bin'),bytes);
  writeFileSync(join(OUT_DIR,id,'exit.txt'),code + '\n');
}
