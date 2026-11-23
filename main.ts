// tiny-vm-01 — a stack virtual machine for make.fun's tiny stack ISA, v1.
// Runs every instance in the input directory, writing its answers out.
import fs from 'node:fs';

const IN_DIR = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

// Traps exit with their code: 2 underflow, 3 overflow, 4 div-by-zero,
// 5 unknown opcode, 6 bad address, 7 call overflow, 8 empty RET, 9 bad pc
// or cut-off immediate, 10 step limit, 11 output limit (writes nothing).
const UNDER = 2, OVER = 3, DIV0 = 4, BADOP = 5, MEM = 6, CALLTRAP = 7,
  RETTRAP = 8, PCTRAP = 9, STEPTRAP = 10, OUT = 11;

// Runs one program to its end: output bytes and exit code.
function run(prog, input) {
  const n = prog.length;
  const S = new Int32Array(256); // data stack, S[0..sp) live
  const C = new Int32Array(64); // call stack, C[0..csp) live
  const M = new Int32Array(256); // memory words, zeroed
  const out = new Uint8Array(65536);
  let sp = 0, csp = 0, olen = 0, ip = 0, pc = 0, steps = 0;
  const end = (code) => ({ bytes: out.subarray(0, olen), code });
  for (;;) {
    // The step's checks, in the ISA's order; the opcode's shape is read off its byte.
    if (steps >= 1000000) return end(STEPTRAP);
    if (pc < 0 || pc >= n) return end(PCTRAP);
    const op = prog[pc];
    const bin = op >= 0x10 && op <= 0x22, ctrl = op >= 0x30 && op <= 0x34;
    const known = op < 8 || (bin && op !== 0x1f) || ctrl || op === 0x40 || op === 0x41 || (op >= 0x50 && op <= 0x53);
    if (!known) return end(BADOP);
    const imm = op === 1 ? 1 : op === 2 ? 4 : op >= 0x30 && op <= 0x33 ? 2 : 0;
    if (pc + imm >= n) return end(PCTRAP);
    steps++;
    const pops = op === 7 ? 3 : op === 5 || op === 6 || op === 0x41 || (bin && op !== 0x17 && op !== 0x1b) ? 2 : op < 3 || (ctrl && op !== 0x31 && op !== 0x32) || op === 0x52 ? 0 : 1;
    if (sp < pops) return end(UNDER);
    // Overflow: a net push (PUSH8, PUSH32, DUP, OVER, IN) at a full stack.
    if (sp === 256 && (op === 1 || op === 2 || op === 4 || op === 6 || op === 0x52)) return end(OVER);
    const next = pc + 1 + imm; pc = next;
    if (bin) {
      // The binary range: NEG and NOT are unary, the rest — ADD SUB MUL DIV
      // MOD DIVU MODU AND OR XOR SHL SHR SHRU EQ LT LTU — take b (the top)
      // and a (under it). DIV/MOD signed (truncated toward zero, remainder
      // takes a's sign); DIVU/MODU/LTU unsigned; shifts use the low 5 bits.
      if (op === 0x17) { S[sp - 1] = -S[sp - 1] | 0; continue; } // NEG
      if (op === 0x1b) { S[sp - 1] = ~S[sp - 1]; continue; } // NOT
      const b = S[sp - 1], a = S[sp - 2];
      if (b === 0 && op >= 0x13 && op <= 0x16) return end(DIV0); // DIV MOD DIVU MODU by zero
      let r;
      switch (op) {
      case 0x10: r = (a + b) | 0; break;
      case 0x11: r = (a - b) | 0; break;
      case 0x12: r = Math.imul(a, b); break;
      case 0x13: r = a === -2147483648 && b === -1 ? a : (a / b) | 0; break;
      case 0x14: r = b === -1 ? 0 : (a % b) | 0; break;
      case 0x15: r = ((a >>> 0) / (b >>> 0)) | 0; break;
      case 0x16: r = ((a >>> 0) % (b >>> 0)) | 0; break;
      case 0x18: r = a & b; break;
      case 0x19: r = a | b; break;
      case 0x1a: r = a ^ b; break;
      case 0x1c: r = a << (b & 31); break;
      case 0x1d: r = a >> (b & 31); break;
      case 0x1e: r = (a >>> (b & 31)) | 0; break;
      case 0x20: r = a === b ? 1 : 0; break;
      case 0x21: r = a < b ? 1 : 0; break;
      default: r = (a >>> 0) < (b >>> 0) ? 1 : 0; break;
      }
      S[sp - 2] = r;
      sp--;
      continue;
    }
    switch (op) {
    case 0x00: return end(0); // HALT
    case 0x01: S[sp++] = (prog[next - 1] << 24) >> 24; break; // PUSH8, sign-extended
    case 0x02: S[sp++] = prog[next - 4] | (prog[next - 3] << 8) | (prog[next - 2] << 16) | (prog[next - 1] << 24); break; // PUSH32
    case 0x03: sp--; break; // POP
    case 0x04: S[sp] = S[sp - 1]; sp++; break; // DUP
    case 0x05: { const t = S[sp - 1]; S[sp - 1] = S[sp - 2]; S[sp - 2] = t; break; } // SWAP
    case 0x06: S[sp] = S[sp - 2]; sp++; break; // OVER
    case 0x07: { const a = S[sp - 3]; S[sp - 3] = S[sp - 2]; S[sp - 2] = S[sp - 1]; S[sp - 1] = a; break; } // ROT
    case 0x30: case 0x31: case 0x32: { // JMP, JZ, JNZ: signed offset from next; target unchecked here
      const rel = ((prog[next - 2] | (prog[next - 1] << 8)) << 16) >> 16;
      let take = op === 0x30;
      if (!take) { const v = S[--sp]; take = op === 0x31 ? v === 0 : v !== 0; }
      if (take) pc = next + rel;
      break;
    }
    case 0x33: // CALL: unsigned absolute target
      if (csp === 64) return end(CALLTRAP);
      C[csp++] = next; pc = prog[next - 2] | (prog[next - 1] << 8); break;
    case 0x34: // RET
      if (csp === 0) return end(RETTRAP);
      pc = C[--csp]; break;
    case 0x40: // LOAD
      if (S[sp - 1] < 0 || S[sp - 1] > 255) return end(MEM);
      S[sp - 1] = M[S[sp - 1]]; break;
    case 0x41: // STORE
      if (S[sp - 1] < 0 || S[sp - 1] > 255) return end(MEM);
      M[S[sp - 1]] = S[sp - 2]; sp -= 2; break;
    case 0x50: { // PRINT: decimal, no padding or newline
      const text = String(S[sp - 1]);
      if (olen + text.length > 65536) return end(OUT);
      sp--;
      for (let i = 0; i < text.length; i++) out[olen++] = text.charCodeAt(i);
      break;
    }
    case 0x51: // PUTC: the low byte
      if (olen + 1 > 65536) return end(OUT);
      out[olen++] = S[--sp] & 255;
      break;
    case 0x52: S[sp++] = ip < input.length ? input[ip++] : -1; break; // IN
    case 0x53: return end(S[--sp] & 255); // EXIT
    }
  }
}

// Answer every instance in the input directory.
for (const id of fs.readdirSync(IN_DIR)) {
  const prog = fs.readFileSync(`${IN_DIR}/${id}/program.bin`);
  let input;
  try { input = fs.readFileSync(`${IN_DIR}/${id}/input.bin`); } catch { input = Buffer.alloc(0); }
  const { bytes, code } = run(prog, input);
  fs.mkdirSync(`${OUT_DIR}/${id}`, { recursive: true });
  fs.writeFileSync(`${OUT_DIR}/${id}/stdout.bin`, bytes);
  fs.writeFileSync(`${OUT_DIR}/${id}/exit.txt`, code + '\n');
}
