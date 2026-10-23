module

public import VerifiedGarbage.TCB.X86.Sse
public import VerifiedGarbage.TCB.X86.Mmx
public import VerifiedGarbage.TCB.Code

/-!
# x86 (32-bit) machine model

**Trusted.** A model of the subset of 32-bit x86 (IA-32, protected mode with
32-bit operand and address size) used by our implementations. Each
instruction's semantics here must agree with the Intel SDM; when adding an
instruction, cite the SDM pseudocode it transcribes.

Modelling choices:
* Registers are the eight 32-bit general-purpose registers. `esp` can be read
  (e.g. to address the arguments on the stack) like any other register.
* Operands are 32 bits wide, apart from byte loads (`movzx`, zero-extending)
  and byte stores. Without a REX prefix (unavailable outside 64-bit mode),
  only `al`, `cl`, `dl` and `bl` can be the source of a byte store as the low
  byte of a 32-bit register (SDM Vol. 1 §3.4.1.1 and Vol. 2 §3.1.1.1), so a
  byte store takes a `Reg8`.
* Legacy SIMD uses only `xmm0`–`xmm7`, each 128 bits (SDM Vol. 1 §10.2.1).
  The model includes no AVX/AVX-512 instructions; legacy writes affect only
  these 128 bits. All XMM registers are caller-saved in the i386 ABI.
* Only CF, ZF, SF and OF are modelled. Each is an `Option Bool`; `none` means
  "undefined" (as the SDM specifies for some instructions). Evaluating a
  branch on an undefined flag faults, so verified code never depends on one.
  PF and AF are not modelled, and no modelled instruction reads them.
* Effective addresses are computed modulo 2³² and zero-extended to the 64-bit
  addresses of `Mem` (segment bases are zero: the flat memory model of every
  mainstream 32-bit OS). Memory accesses must lie within the state's permitted
  regions: loads within `rd ++ wr`, stores within `wr`; otherwise the
  instruction faults. Memory is little-endian.
* The baseline is i686 as Rust's `i686-*` targets define it: a Pentium 4 or
  later, with SSE2 (the Rust crate refuses to build for 32-bit x86 without
  SSE2). Older CPUs are not supported: the 80386 and 80486 multiply in a
  time that depends on the multiplier (Intel 80386 Programmer's Reference
  Manual, "MUL": "an early-out multiply algorithm").
* Instructions whose timing depends on their operands (e.g. `div`) must never
  be added: the constant-time leakage model assumes they do not exist. `mul`
  is one of the instructions whose timing Intel documents as independent of
  their data operands on its Core and Atom processors ("Data Operand
  Independent Timing Instruction Set Architecture (ISA) Guidance", which
  lists `MUL`).
* Assumed, not proven: that holds on every processor that runs this code.
  Intel's guidance covers only its Core and Atom processors, while the
  baseline also admits processors it does not cover: the NetBurst Pentium 4
  and its Xeons, and those of AMD, VIA and Zhaoxin, whose vendors document
  no such list. On Intel Core processors from Ice Lake and Intel Atom
  processors from Gracemont on, it holds only while the DOITM bit
  (IA32_UARCH_MISC_CTL[0], MSR 1B01H) is set, which resets to 0 and only
  privileged software can set: user code runs with it clear unless the
  operating system sets it (see `TCB/X86_64/Isa.lean`).
* Calls (`call`) and returns (`ret`) are near and direct (SDM Vol. 2, "CALL",
  "RET"). The return addresses are the next of the state's `unknowns`,
  which nothing constrains (see `TCB/Code.lean`).
* `symPush` obtains a static's position-independent address with a near
  call to the next instruction, a load of that return address, and an ADD
  of the link-time difference to the static (`State.syms`). Its four-byte
  stack slot is an explicit frame, released by `free 4`. No instruction
  changes `syms`. The CALL rel32 with displacement zero does not push a
  shadow-stack entry (SDM Vol. 2, CALL pseudocode, `DEST != 0`), so the
  sequence also works with CET shadow stacks enabled.
* `push` and `pop` (of registers other than `esp`) only occur as the push
  and pop of a frame (see `push`), as a sequence of them.
* A frame may instead allocate a buffer of `bytes` bytes on the stack
  (`alloc`, `lea esp, [esp - bytes]`), released by its pop (`free`, `lea
  esp, [esp + bytes]`); `lea` writes only `esp`, so neither changes the
  flags or memory. `bytes` is positive, a multiple of 4 and less than 4096,
  as for the frames of the x86-64 and AArch64 models: less than a page, so
  that the allocation does not move `esp` past a guard page below the stack.
* MMX (`TCB/X86/Mmx.lean`): the eight 64-bit MMX registers alias the x87
  data registers, and every MMX instruction but EMMS makes the x87 tag word
  all valid (SDM Vol. 1 §9.5.1). The System V i386 ABI requires the x87
  stack to be empty on entry, on return and at a call ("The CPU shall be in
  x87 mode upon entry to a function. Therefore, every function that uses the
  MMX registers is required to issue an emms or femms instruction after
  using MMX registers, before returning or calling another function.",
  Intel386 psABI, "Registers"). So MMX instructions run only inside an *MMX
  frame*, `frame mmxEnter body emms` (see `TCB/Code.lean`), and fault
  outside one: a stack frame of no bytes, whose push `mmxEnter` emits no
  instruction and enters MMX mode (`State.mmx`; MMX frames do not nest),
  and whose pop is `emms` (SDM
  Vol. 2, "EMMS": `x87FPUTagWord := FFFFH`), which leaves it, with `esp`
  and the writable regions as the push left them. So every MMX instruction
  is followed by an `emms` before the function returns, and the x87 stack
  is empty then whenever it was on entry. A call inside an MMX frame is not
  excluded: the functions this code calls are its own (`call` names a
  function emitted with it), which touch the x87 registers only in MMX
  frames of their own, and those fault inside one (frames do not nest), so
  no execution has a callee use them while its caller's MMX values are
  live. No modelled instruction reads or writes the x87 registers
  otherwise; the MMX registers are caller-saved (the x87 registers are
  scratch registers in the ABI), and their values on entry are unknown.
* MXCSR-configuration-dependent timing (MCDT): on some Intel processors,
  `pmuludq`, although on Intel's DOIT list, may take up to a cycle longer
  to retire for specific data values unless MXCSR holds `0x1FBF` (Intel,
  "MXCSR Configuration Dependent Timing", and its list of the instructions
  affected, "MCDT Data Operand Independent Timing Instructions"; the
  processors that enumerate `MCDT_NO`, CPUID.(EAX=7H,ECX=2):EDX[5], are not
  affected). The leakage model does not see this, so `pmuludq` runs only
  inside an *MCDT frame*, `frame (mcdtEnter r) body mcdtLeave`, and faults
  outside one. The frame is a stack frame of 12 bytes around Intel's
  mitigation: its push is `lea esp, [esp - 12]`, then the prologue,
  `stmxcsr DWORD PTR [esp + 4]` (SDM Vol. 2, "STMXCSR": `m32 := MXCSR`),
  `mov r, 0x1FBF`, `mov DWORD PTR [esp], r`, `ldmxcsr DWORD PTR [esp]`
  (SDM Vol. 2, "LDMXCSR": `MXCSR := m32`; `0x1FBF` sets no reserved bit,
  bits 31:16) and `lfence`; its pop is the epilogue, `lfence` and `ldmxcsr
  DWORD PTR [esp + 4]`, then `lea esp, [esp + 12]`. `lfence` (SDM Vol. 2,
  "LFENCE") has no architectural effect.

  MXCSR is modelled by the number of open MCDT frames (`State.mcdt`) and
  its value outside them (`State.mxcsr`), which no instruction changes:
  inside one MXCSR holds `0x1FBF`, which no modelled instruction reads
  (integer and `pmuludq` instructions raise no SIMD floating-point
  exceptions). So the push saves `State.mxcsr` outside an MCDT frame and
  `0x1FBF` inside one (frames may nest, as a callee may open one inside its
  caller's), and the pop faults unless the word it loads into MXCSR is the
  value that leaves it as it was before the push. A frame's region is 9
  bytes (the two words at its bottom, and a byte of its padding): a length
  that is no multiple of 4, unlike every other frame's, so no other pop
  (`free`, `pop`, `emms`) can remove an MCDT frame, and `mcdtLeave` removes
  no other frame. Every execution that returns therefore leaves MXCSR as it
  was on entry (its control bits are callee-saved in the System V i386 ABI;
  `abiPreserved` need not mention it, as with the x87 state of MMX frames),
  and every `pmuludq` runs between Intel's prologue and epilogue.
  `ci/check_mcdt.py` also checks this in the generated code.
-/

@[expose] public section

namespace VG.X86

/-- The registers whose low byte has an 8-bit name without a REX prefix:
`al`, `cl`, `dl`, `bl` (the low bytes of `eax`, `ecx`, `edx`, `ebx`). -/
inductive Reg8
  | al | cl | dl | bl
  deriving DecidableEq, Repr

/-- The 32-bit register whose low byte a `Reg8` is. -/
def Reg8.reg : Reg8 → Reg
  | .al => .eax | .cl => .ecx | .dl => .edx | .bl => .ebx

inductive Src
  | reg (r : Reg)
  | imm (v : BitVec 32)
  | mem (m : MemOp)
  deriving DecidableEq, Repr

inductive AluOp | add | adc | sub | sbb | and | or | xor | cmp | test
  deriving DecidableEq, Repr

inductive ShiftOp | ror | shr
  deriving DecidableEq, Repr

inductive Instr
  /-- Position-independent address of a static, as the push of a four-byte
  frame: `call 2f; 2: mov dst, [esp]; add dst, offset name - 2b`.
  `dst` must not be `esp`; release the frame with `free 4`. -/
  | symPush (dst : Reg) (name : String)
  /-- `mov dst, src` -/
  | mov (dst : Reg) (src : Src)
  /-- `mov DWORD PTR [dst], src` -/
  | store (dst : MemOp) (src : Reg)
  /-- Two-operand ALU instruction `op dst, src`. -/
  | alu (op : AluOp) (dst : Reg) (src : Src)
  /-- `op dst, count` with an immediate count. Only counts `1 ≤ count ≤ 31` are
  modelled; any other count faults. -/
  | shift (op : ShiftOp) (dst : Reg) (count : Nat)
  /-- `bswap dst` -/
  | bswap (dst : Reg)
  /-- `movzx dst, BYTE PTR [src]`: the byte, zero-extended. -/
  | movzx8 (dst : Reg) (src : MemOp)
  /-- `mov BYTE PTR [dst], src`: the low byte of `src.reg`. -/
  | store8 (dst : MemOp) (src : Reg8)
  /-- `push r` for each `r` of `rs`, in order: the push of a frame (see
  `push`); `rs` must not be empty or contain `esp` -/
  | push (rs : List Reg)
  /-- `pop r`, `k` times: the pop of a frame of `4 * k` bytes (see `pop`);
  `k > 0`, and `r` is not `esp` -/
  | pop (r : Reg) (k : Nat)
  /-- `lea esp, [esp - bytes]` (8D /r): the push of a frame of `bytes` bytes
  that it does not write (see `push`); `0 < bytes < 4096`, a multiple of 4 -/
  | alloc (bytes : Nat)
  /-- `lea esp, [esp + bytes]` (8D /r): the pop of a frame of `bytes` bytes
  (see `pop`) -/
  | free (bytes : Nat)
  /-- `mul r32` (F7 /4): the unsigned product `EDX:EAX := EAX * r32`. -/
  | mul (src : Reg)
  /-- Legacy SSE2 unaligned 128-bit load (F3 0F 6F /r). -/
  | movdquLoad (dst : XReg) (src : MemOp)
  /-- Legacy SSE2 unaligned 128-bit store (F3 0F 7F /r). -/
  | movdquStore (dst : MemOp) (src : XReg)
  /-- `movq xmm, QWORD PTR [m]` (F3 0F 7E /r): a 64-bit load into the low
  quadword, zeroing the high one. -/
  | movqLoad (dst : XReg) (src : MemOp)
  /-- `movq QWORD PTR [m], xmm` (66 0F D6 /r): a 64-bit store of the low
  quadword. -/
  | movqStore (dst : MemOp) (src : XReg)
  /-- A legacy SSE instruction that writes only an XMM register. -/
  | xop (op : XOp)
  /-- An MMX instruction that writes only an MMX or XMM register
  (`TCB/X86/Mmx.lean`); it faults outside an MMX frame. -/
  | mop (op : MOp)
  /-- `movq QWORD PTR [m], mm` (NP 0F 7F /r): a 64-bit store; it faults
  outside an MMX frame. -/
  | mmxStore (dst : MemOp) (src : MReg)
  /-- The push of an MMX frame: no instruction; enters the frame (see
  `push`). -/
  | mmxEnter
  /-- `pmuludq dst, src` (66 0F F4 /r, `pmuludq` in `TCB/X86/Sse.lean`); it
  faults outside an MCDT frame. -/
  | pmuludq (dst src : XReg)
  /-- The push of an MCDT frame (see `push`): `lea esp, [esp - 12]`,
  `stmxcsr DWORD PTR [esp + 4]`, `mov r, 0x1FBF`, `mov DWORD PTR [esp], r`,
  `ldmxcsr DWORD PTR [esp]`, `lfence`. -/
  | mcdtEnter (r : Reg)
  /-- The pop of an MCDT frame (see `pop`): `lfence`, `ldmxcsr DWORD PTR
  [esp + 4]`, `lea esp, [esp + 12]`. -/
  | mcdtLeave
  /-- `emms` (NP 0F 77): the pop of an MMX frame (see `pop`). -/
  | emms
  deriving DecidableEq, Repr

/-- Branch conditions (`jcc` suffixes). -/
inductive Cond
  /-- `je`: ZF = 1 -/
  | e
  /-- `jne`: ZF = 0 -/
  | ne
  /-- `jb`: CF = 1 -/
  | b
  /-- `jae`: CF = 0 -/
  | ae
  deriving DecidableEq, Repr



def readSrc (s : State) : Src → Option (BitVec 32)
  | .reg r => some (s.gpr r)
  | .imm v => some v
  | .mem m => s.load32 (s.ea m)

def srcAddrs (s : State) : Src → List Addr
  | .mem m => [s.ea m]
  | _ => []

/-- Flags after the result `r` of an arithmetic or logic operation with carry
`c` and signed overflow `o`: ZF and SF are computed from `r`. -/
def arithFlags (s : State) (r : BitVec 32) (c o : Bool) : State :=
  s.setFlags (some c) (some o) (some (r == 0)) (some r.msb)

/-- Signed overflow of `a + b (+ carry) = r`. -/
def addOverflow (a b r : BitVec 32) : Bool := a.msb == b.msb && r.msb != a.msb
/-- Signed overflow of `a - b (- borrow) = r`. -/
def subOverflow (a b r : BitVec 32) : Bool := a.msb != b.msb && r.msb != a.msb

/-- SDM Vol. 2: ADD, ADC, SUB, SBB, CMP set CF/OF/ZF/SF by the result; AND,
OR, XOR, TEST clear CF and OF and set ZF/SF by the result. CMP and TEST write
no register. -/
def execAlu (op : AluOp) (dst : Reg) (src : Src) (s : State) : Option State :=
  (readSrc s src).bind fun b =>
  let a := s.gpr dst
  match op with
  | .add => let r := a + b
    some ((arithFlags s r (2 ^ 32 ≤ a.toNat + b.toNat) (addOverflow a b r)).setReg dst r)
  | .adc => s.cf.map fun c =>
    let r := a + b + (BitVec.ofBool c).setWidth 32
    (arithFlags s r (2 ^ 32 ≤ a.toNat + b.toNat + c.toNat) (addOverflow a b r)).setReg dst r
  | .sub => let r := a - b
    some ((arithFlags s r (a.toNat < b.toNat) (subOverflow a b r)).setReg dst r)
  | .sbb => s.cf.map fun c =>
    let r := a - b - (BitVec.ofBool c).setWidth 32
    (arithFlags s r (a.toNat < b.toNat + c.toNat) (subOverflow a b r)).setReg dst r
  | .cmp => let r := a - b
    some (arithFlags s r (a.toNat < b.toNat) (subOverflow a b r))
  | .and => let r := a &&& b; some ((arithFlags s r false false).setReg dst r)
  | .or => let r := a ||| b; some ((arithFlags s r false false).setReg dst r)
  | .xor => let r := a ^^^ b; some ((arithFlags s r false false).setReg dst r)
  | .test => let r := a &&& b; some (arithFlags s r false false)

/-- SDM Vol. 2, "RCL/RCR/ROL/ROR" and "SAL/SAR/SHL/SHR", for a 32-bit
operand and a count `n` with `1 ≤ n ≤ 31` (so the masked count `n AND 1FH`
is `n`; other counts fault):

* ROR: the operand is rotated right by `n`; CF := MSB of the result; OF :=
  MSB XOR MSB−1 of the result if `n = 1`, otherwise undefined; SF and ZF are
  unaffected.
* SHR: the operand is shifted right (logically) by `n`; CF := the last bit
  shifted out (bit `n − 1` of the operand); OF := MSB of the original operand
  if `n = 1`, otherwise undefined; SF and ZF are set according to the result.

(AF and PF are not modelled.) -/
def execShift (op : ShiftOp) (dst : Reg) (n : Nat) (s : State) : Option State :=
  if 1 ≤ n ∧ n ≤ 31 then
    let a := s.gpr dst
    match op with
    | .ror => let r := a.rotateRight n
      some ((s.setFlags (some r.msb) (if n = 1 then some (r.msb ^^ r.getMsbD 1) else none)
        s.zf s.sf).setReg dst r)
    | .shr => let r := a >>> n
      some ((s.setFlags (some (a.getLsbD (n - 1))) (if n = 1 then some a.msb else none)
        (some (r == 0)) (some r.msb)).setReg dst r)
  else none

/-- SDM Vol. 2, "BSWAP": `DEST[7:0] := TEMP[31:24]; DEST[15:8] := TEMP[23:16];
DEST[23:16] := TEMP[15:8]; DEST[31:24] := TEMP[7:0]`. No flags are affected. -/
def bswap (a : BitVec 32) : BitVec 32 :=
  a.extractLsb' 0 8 ++ a.extractLsb' 8 8 ++ a.extractLsb' 16 8 ++ a.extractLsb' 24 8

/-- SDM Vol. 2, "MUL—Unsigned Multiply", for a 32-bit operand: `EDX:EAX :=
EAX ∗ SRC` (the 64-bit product of the unsigned operands, its high half in
EDX and its low half in EAX). "The OF and CF flags are set to 0 if the upper
half of the result is 0; otherwise, they are set to 1. The SF, ZF, AF, and PF
flags are undefined." (AF and PF are not modelled.) -/
def execMul (src : Reg) (s : State) : State :=
  let p := (s.gpr .eax).toNat * (s.gpr src).toNat
  let hi : BitVec 32 := BitVec.ofNat 32 (p / 2 ^ 32)
  ((s.setFlags (some (hi != 0)) (some (hi != 0)) none none).setReg .eax (BitVec.ofNat 32 p)).setReg
    .edx hi

/-- Semantics of an instruction. The byte forms: SDM Vol. 2, "MOVZX":
`DEST := ZeroExtend(SRC)`, and "MOV": `DEST := SRC`, where the source of a
byte store is the low byte of `eax`, `ecx`, `edx` or `ebx` (AL, CL, DL, BL;
SDM Vol. 1 §3.4.1.1). Neither affects the flags. The quadword moves: SDM
Vol. 2, "MOVQ—Move Quadword", `MOVQ xmm1, m64` (F3 0F 7E /r): `DEST[63:0] :=
SRC[63:0]; DEST[127:64] := 0000000000000000H`, and `MOVQ m64, xmm1` (66 0F
D6 /r): `DEST[63:0] := SRC[63:0]`; neither affects the flags, and a 64-bit
memory operand of a legacy SSE instruction needs no alignment. -/
def exec : Instr → State → Option State
  | .mov d src, s => (readSrc s src).map fun v => s.setReg d v
  | .store m r, s => s.store32 (s.ea m) (s.gpr r)
  | .alu op d src, s => execAlu op d src s
  | .shift op d n, s => execShift op d n s
  | .bswap d, s => some (s.setReg d (bswap (s.gpr d)))
  | .movzx8 d m, s => (s.load8 (s.ea m)).map fun v => s.setReg d (v.setWidth 32)
  | .store8 m r, s => s.store8 (s.ea m) ((s.gpr r.reg).setWidth 8)
  | .mul r, s => some (execMul r s)
  | .movdquLoad d m, s => (s.load128 (s.ea m)).map fun v => s.setXmm d v
  | .movdquStore m r, s => s.store128 (s.ea m) (s.xmm r)
  | .movqLoad d m, s => (s.load64 (s.ea m)).map fun v => s.setXmm d ((0 : BitVec 64) ++ v)
  | .movqStore m r, s => s.store64 (s.ea m) ((s.xmm r).extractLsb' 0 64)
  | .xop op, s => some (op.exec s)
  | .mop op, s => op.exec s
  | .mmxStore m r, s => if s.mmx then s.store64 (s.ea m) (s.mm r) else none
  | .pmuludq d r, s => if 0 < s.mcdt then some (s.setXmm d (pmuludq (s.xmm d) (s.xmm r))) else none
  -- Only the push and pop of a frame (`push`, `pop`).
  | .symPush .., _ | .push _, _ | .pop .., _ | .alloc _, _ | .free _, _ | .mmxEnter, _ | .emms, _
  | .mcdtEnter _, _ | .mcdtLeave, _ => none

def addrs : Instr → State → List Addr
  | .symPush .., s => [(s.gpr .esp - 4).setWidth 64, (s.gpr .esp - 4).setWidth 64]
  | .mov _ src, s => srcAddrs s src
  | .store m _, s => [s.ea m]
  | .alu _ _ src, s => srcAddrs s src
  | .shift .., _ => []
  | .bswap _, _ => []
  | .movzx8 _ m, s => [s.ea m]
  | .store8 m _, s => [s.ea m]
  | .mul _, _ | .xop _, _ => []
  | .mop op, s => op.addrs s
  | .mmxStore m _, s => [s.ea m]
  | .mmxEnter, _ | .emms, _ | .pmuludq .., _ => []
  -- `stmxcsr`, then the store and `ldmxcsr` of `0x1FBF`, below `esp`.
  | .mcdtEnter _, s =>
    [(s.gpr .esp - 8).setWidth 64, (s.gpr .esp - 12).setWidth 64, (s.gpr .esp - 12).setWidth 64]
  | .mcdtLeave, s => [(s.gpr .esp + 4).setWidth 64]
  | .movdquLoad _ m, s | .movdquStore m _, s => [s.ea m]
  | .movqLoad _ m, s | .movqStore m _, s => [s.ea m]
  | .push rs, s => (List.range rs.length).map fun i =>
    (s.gpr .esp - BitVec.ofNat 32 (4 * (i + 1))).setWidth 64
  | .pop _ k, s => (List.range k).map fun i =>
    (s.gpr .esp + BitVec.ofNat 32 (4 * i)).setWidth 64
  | .alloc _, _ | .free _, _ => []

/-- SDM Vol. 2, "Jcc": JE jumps if ZF = 1, JNE if ZF = 0, JB if CF = 1 and
JAE if CF = 0. -/
def eval : Cond → State → Option Bool
  | .e, s => s.zf
  | .ne, s => s.zf.map (!·)
  | .b, s => s.cf
  | .ae, s => s.cf.map (!·)

/-- SDM Vol. 2, "CALL", near call with a 32-bit operand size: `ESP := ESP −
4; Memory[ESP] := EIP` (`Push(EIP)`, where `EIP` is the address of the next
instruction), then the jump. No flags are affected. The return address is
the next of the state's. -/
def call (s : State) : Option State :=
  let sp := s.gpr .esp - 4
  some { s.setReg .esp sp with
    mem := s.mem.writeW (sp.setWidth 64) (s.unknowns 0)
    unknowns := fun n => s.unknowns (n + 1) }

/-- SDM Vol. 2, "RET", near return with a 32-bit operand size: `EIP :=
Pop()`, i.e. `EIP := Memory[ESP]; ESP := ESP + 4`. No flags are affected. It
returns after the call instruction if `ESP` and the return address at
`[ESP]` are those the call left (`s₁`); otherwise the model faults. -/
def ret (s₁ s₂ : State) : Option State :=
  if s₂.gpr .esp = s₁.gpr .esp ∧
      s₂.mem.readW ((s₂.gpr .esp).setWidth 64) 32 = s₁.mem.readW ((s₁.gpr .esp).setWidth 64) 32 then
    some (s₂.setReg .esp (s₂.gpr .esp + 4))
  else none

/-- `push r` for each of `rs`, in order, where `r ≠ esp`: SDM Vol. 2,
"PUSH", 32-bit operand size: `ESP := ESP − 4; Memory[SS:ESP] := SRC`. No
flags are affected. -/
def pushRegs (s : State) : List Reg → State
  | [] => s
  | r :: rs =>
    let sp := s.gpr .esp - 4
    pushRegs { s.setReg .esp sp with mem := s.mem.writeW (sp.setWidth 64) (s.gpr r) } rs

/-- `pop r`, `k` times, where `r ≠ esp`: SDM Vol. 2, "POP", 32-bit operand
size: `DEST := SS:ESP; ESP := ESP + 4`. No flags are affected. -/
def popReg (s : State) (r : Reg) : Nat → State
  | 0 => s
  | k + 1 =>
    popReg ((s.setReg r (s.mem.readW ((s.gpr .esp).setWidth 64) 32)).setReg .esp
      (s.gpr .esp + 4)) r k

/-- MXCSR with `n` MCDT frames open, its value outside them being `v`. -/
def mcdtSaved (n : Nat) (v : BitVec 32) : BitVec 32 := if n = 0 then v else 0x1FBF

/-- The push of a frame: `push r` for each `r` of `rs` (`pushRegs`). The
`4 * rs.length` bytes it stores become a writable region, at the head of
`wr`. Faults if `rs` is empty or contains `esp`, or if the frame would wrap
around the address space.

Or `lea esp, [esp - bytes]` (`alloc`): SDM Vol. 2, "LEA—Load Effective
Address", with a 32-bit operand size and address size: `DEST :=
EffectiveAddress(SRC)`, the address computed modulo 2³²; "Flags Affected:
None". The `bytes` bytes below `esp` become a writable region, at the head
of `wr`, which it does not write: they hold what memory held there, as the
bytes a call or a push stores below `esp` before it does (and a contract
says nothing of them: they are in the stack below the caller's stack
pointer, `Abi.reserved`). Faults unless `0 < bytes < 4096` and `bytes` is a
multiple of 4, or if the frame would wrap around the address space.

Or the push of an MMX frame (`mmxEnter`, no instruction): a frame of no
bytes (the empty region at `esp`, at the head of `wr`; `esp` and memory
unchanged), which enters MMX mode (`State.mmx`), faulting inside one.

Or the push of an MCDT frame (`mcdtEnter r`, Intel's prologue): `lea esp,
[esp - 12]` (as `alloc`), whose first 9 bytes become a writable region, at
the head of `wr`; `stmxcsr` stores MXCSR to the word at `esp + 4`: the
value outside MCDT frames (`State.mxcsr`) if none is open, `0x1FBF`
otherwise; `mov` sets `r` to `0x1FBF` and stores it to the word at `esp`,
which `ldmxcsr` loads into MXCSR; `lfence` has no architectural effect. It
opens an MCDT frame (`State.mcdt`), faulting if `r` is `esp` or if the
frame would wrap around the address space; no flags are affected (SDM Vol.
2, "LEA", "STMXCSR", "MOV", "LDMXCSR", "LFENCE"). -/
def push : Instr → State → Option State
  -- Intel SDM Vol. 2, CALL (near, rel32), MOV (r32, r/m32), and ADD
  -- (r32, imm32). CALL pushes the next EIP; MOV reads it; ADD adds the
  -- link-time displacement from that EIP to the static, modulo 2^32.
  -- ADD sets the flags, as in execAlu. The stored EIP is an unknown, and
  -- its slot remains part of memory. The frame accounts for its stack use.
  | .symPush d name, s =>
    if d ≠ .esp ∧ 4 ≤ (s.gpr .esp).toNat then
      let sp := s.gpr .esp - 4
      let pc := s.unknowns 0
      let delta := s.syms name - pc
      let t := arithFlags s (s.syms name) (2 ^ 32 ≤ pc.toNat + delta.toNat)
        (addOverflow pc delta (s.syms name))
      some { (t.setReg .esp sp).setReg d (s.syms name) with
        mem := s.mem.writeW (sp.setWidth 64) (s.unknowns 0)
        unknowns := fun n => s.unknowns (n + 1)
        wr := ⟨sp.setWidth 64, 4⟩ :: s.wr }
    else none
  | .mmxEnter, s =>
    if s.mmx then none else some { s with mmx := true, wr := ⟨(s.gpr .esp).setWidth 64, 0⟩ :: s.wr }
  | .mcdtEnter r, s =>
    if r ≠ .esp ∧ 12 ≤ (s.gpr .esp).toNat then
      let sp := s.gpr .esp - 12
      some { (s.setReg .esp sp).setReg r 0x1FBF with
        mem := (s.mem.writeW ((s.gpr .esp - 8).setWidth 64) (mcdtSaved s.mcdt s.mxcsr)).writeW
          (sp.setWidth 64) (0x1FBF : BitVec 32)
        mcdt := s.mcdt + 1, wr := ⟨sp.setWidth 64, 9⟩ :: s.wr }
    else none
  | .alloc bytes, s =>
    if 0 < bytes ∧ bytes < 4096 ∧ bytes % 4 = 0 ∧ bytes ≤ (s.gpr .esp).toNat then
      let sp := s.gpr .esp - BitVec.ofNat 32 bytes
      some { s.setReg .esp sp with wr := ⟨sp.setWidth 64, bytes⟩ :: s.wr }
    else none
  | .push rs, s =>
    let n := 4 * rs.length
    if rs ≠ [] ∧ .esp ∉ rs ∧ n ≤ (s.gpr .esp).toNat then
      some { pushRegs s rs with
        wr := ⟨(s.gpr .esp - BitVec.ofNat 32 n).setWidth 64, n⟩ :: s.wr }
    else none
  | _, _ => none

/-- The pop of a frame: `pop r`, `k` times (`popReg`), so that `r` holds the
last word of the frame. Faults if `k = 0` or `r` is `esp`, and unless `esp`
and the writable regions are those the push left (`s₁`), and the frame, the
region at their head, has `4 * k` bytes; it removes the frame.

Or `lea esp, [esp + bytes]` (`free`, "LEA" as for `alloc`), with the same
conditions on `bytes` as `alloc` and on `esp` and the writable regions as
`pop`, the frame having `bytes` bytes; it changes neither memory nor any
other register.

Or `emms`, the pop of an MMX frame: SDM Vol. 2, "EMMS": `x87FPUTagWord :=
FFFFH` (the x87 stack empty); "Flags Affected: None". It leaves the frame,
faulting unless the code is in one and `esp` and the writable regions are
those the push left (`s₁`) with the empty frame at their head, which it
removes; it changes no register or memory.

Or `mcdtLeave`, the pop of an MCDT frame (Intel's epilogue): `lfence`, no
architectural effect, then `ldmxcsr DWORD PTR [esp + 4]` (SDM Vol. 2,
"LDMXCSR": `MXCSR := m32`), then `lea esp, [esp + 12]` (as `free`). It
closes the frame, faulting unless one is open, `esp` and the writable
regions are those the push left (`s₁`) with the frame's region of 9 bytes
at their head, which it removes, and the word at `esp + 4` is the value
MXCSR had before the push (`mcdtSaved`); it changes no other register, no
memory and no flags (SDM Vol. 2, "LDMXCSR", "LFENCE", "LEA"). -/
def pop : Instr → State → State → Option State
  | .emms, s₁, s₂ =>
    if s₂.mmx ∧ s₂.gpr .esp = s₁.gpr .esp ∧ s₂.wr = s₁.wr ∧
        s₁.wr.head? = some ⟨(s₁.gpr .esp).setWidth 64, 0⟩ then
      some { s₂ with mmx := false, wr := s₂.wr.tail }
    else none
  | .mcdtLeave, s₁, s₂ =>
    if 0 < s₂.mcdt ∧ s₂.gpr .esp = s₁.gpr .esp ∧ s₂.wr = s₁.wr ∧
        s₁.wr.head? = some ⟨(s₁.gpr .esp).setWidth 64, 9⟩ ∧
        s₂.mem.readW ((s₂.gpr .esp + 4).setWidth 64) 32 = mcdtSaved (s₂.mcdt - 1) s₂.mxcsr then
      some { s₂.setReg .esp (s₂.gpr .esp + 12) with mcdt := s₂.mcdt - 1, wr := s₂.wr.tail }
    else none
  | .free bytes, s₁, s₂ =>
    if 0 < bytes ∧ bytes < 4096 ∧ bytes % 4 = 0 ∧ s₂.gpr .esp = s₁.gpr .esp ∧ s₂.wr = s₁.wr ∧
        s₁.wr.head? = some ⟨(s₁.gpr .esp).setWidth 64, bytes⟩ then
      some { s₂.setReg .esp (s₂.gpr .esp + BitVec.ofNat 32 bytes) with wr := s₂.wr.tail }
    else none
  | .pop r k, s₁, s₂ =>
    if k ≠ 0 ∧ r ≠ .esp ∧ s₂.gpr .esp = s₁.gpr .esp ∧ s₂.wr = s₁.wr ∧
        s₁.wr.head? = some ⟨(s₁.gpr .esp).setWidth 64, 4 * k⟩ then
      some { popReg s₂ r k with wr := s₂.wr.tail }
    else none
  | _, _, _ => none

/-- The register an instruction writes, if it writes exactly one (the pop of
a frame also moves `esp`, as the push does): `mul` writes two, `eax` and
`edx`, and stores none. -/
def Instr.dst : Instr → Option Reg
  | .symPush d _ | .mcdtEnter d => some d
  | .mov d _ | .alu _ d _ | .shift _ d _ | .bswap d | .movzx8 d _ | .pop d _ => some d
  | .store .. | .store8 .. | .push _ | .mul _ | .movdquLoad .. | .movdquStore .. | .xop _
  | .movqLoad .. | .movqStore .. | .mop _ | .mmxStore .. | .mmxEnter | .emms
  | .alloc _ | .free _ | .pmuludq .. | .mcdtLeave => none

/-- Intel SDM Vol. 2's "CPUID Feature Flag" column: PSHUFB/PALIGNR need
SSSE3, SHA256MSG1/MSG2/RNDS2 and SHA1MSG1/MSG2/NEXTE/RNDS4 need SHA,
AESENC/AESENCLAST/AESDEC/AESDECLAST/AESIMC/AESKEYGENASSIST need AES
(`66 0F 38 DC /r`, `66 0F 38 DD /r`, `66 0F 38 DE /r`, `66 0F 38 DF /r`,
`66 0F 38 DB /r`, `66 0F 3A DF /r ib`), and PCLMULQDQ needs PCLMULQDQ.
The remaining legacy instructions (among them PADDQ, PMULUDQ, PSHUFLW,
PSHUFHW, MOVQ and LFENCE) are SSE2, STMXCSR and LDMXCSR are SSE, and the
MMX instructions MMX or SSE2, all already in this target's i686
baseline. -/
def Instr.requires : Instr → List String
  | .xop (.bin .pshufb ..) | .xop (.palignr ..) => ["ssse3"]
  | .xop (.bin .sha256msg1 ..) | .xop (.bin .sha256msg2 ..)
    | .xop (.sha256rnds2 ..) | .xop (.bin .sha1msg1 ..) | .xop (.bin .sha1msg2 ..)
    | .xop (.bin .sha1nexte ..) | .xop (.sha1rnds4 ..) => ["sha"]
  | .xop (.bin .aesenc ..) | .xop (.bin .aesenclast ..) | .xop (.bin .aesdec ..)
    | .xop (.bin .aesdeclast ..) | .xop (.bin .aesimc ..) | .xop (.aeskeygenassist ..) => ["aes"]
  | .xop (.pclmulqdq ..) => ["pclmulqdq"]
  | _ => []

abbrev isa : ISA where
  State := State
  Instr := Instr
  Cond := Cond
  exec := exec
  addrs := addrs
  eval := eval
  call := call
  callAddrs s := [(s.gpr .esp - 4).setWidth 64]
  ret := ret
  retAddrs s := [(s.gpr .esp).setWidth 64]
  -- Other than as the push and pop of a frame. `mul` writes `eax` and `edx`,
  -- never `esp`.
  writesSp i := i.dst == some .esp
  push := push
  pop := pop
  -- SSE2 is baseline; the crypto and SSSE3 instructions require their CPUID features.
  requires := Instr.requires

end VG.X86
