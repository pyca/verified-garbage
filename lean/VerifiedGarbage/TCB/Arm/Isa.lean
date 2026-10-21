module

public import VerifiedGarbage.TCB.Code

/-!
# ARMv7 machine model

**Trusted.** A model of the subset of 32-bit ARMv7-A used by our
implementations. Each instruction's semantics here must agree with the ARM
Architecture Reference Manual, ARMv7-A and ARMv7-R edition (DDI 0406C),
chapter A8 ("Instruction Details"); when adding an instruction, cite the
section whose pseudocode it transcribes.

Modelling choices:
* Only instructions that exist, with the same semantics, in both the ARM
  (A32) and the Thumb (T32) instruction sets are modelled, so the model is
  right whichever of the two a function is assembled in.
* Registers are `r0`–`r12` and `lr` (`r14`); `sp` is separate. Frame delimiters
  (`push`/`pop`, `alloc`/`free`) alone write it. They, `addSp`, and
  `ldr t, [sp, #off]` (for arguments passed on the stack)
  read it; `pc` is not an operand.
* The stack pointer is always word-aligned (AAPCS §5.2.1.1, "SP mod 4 = 0"),
  and a frame moves it by whole words, so the model does not check the
  alignment that `push` requires (DDI 0406C: `MemA`).
* Only the N, Z, C and V flags are modelled.
* Immediates that an A32 instruction cannot encode make the instruction
  fault, so verified code only contains encodable instructions. (A T32
  encoding exists for fewer modified immediates; one that is missing is an
  assembler error, not a different meaning.) Shift amounts are `1`–`31`.
* Addresses are 32 bits (computed modulo 2³²) and zero-extended to the 64-bit
  addresses of `Mem`. Memory accesses must lie within the state's permitted
  regions: loads within `rd ++ wr`, stores within `wr`; otherwise the
  instruction faults. Memory is little-endian.
* Word loads and stores (`ldr`, `str`) need no alignment, and the code does
  them on byte buffers at any address. ARMv7 supports unaligned `LDR` and
  `STR` to Normal memory when alignment checking is off (`SCTLR.A` = 0 on
  ARMv7-A and -R: DDI 0406C.d A3.2.1, "Unaligned data access", Table A3-1;
  `CCR.UNALIGN_TRP` = 0 on ARMv7-M: DDI 0403E.b A3.2.1, "Alignment
  behavior"). An unaligned access to Device or Strongly-ordered memory is not
  permitted: it faults, or without the Virtualization Extensions is
  UNPREDICTABLE (DDI 0406C.d A3.2.2); and with the stage 1 MMU disabled every
  data access is Strongly-ordered (DDI 0406C.d B3.2.1). Linux, Android and
  the other hosted targets run user code with alignment checking off over
  Normal memory. A bare-metal program (e.g. on `armv7a-none-eabi`, which
  Rust builds with `+strict-align` for this reason) must do the same: turn
  alignment checking off and run the code with the MMU on, with every buffer
  it passes in Normal memory. The model does not describe any other setting.
* Instructions whose timing depends on their operands (e.g. `sdiv`, `udiv`)
  must never be added: the constant-time leakage model assumes they do not
  exist. ARMv7 makes no architectural promise about multiply timing (it has
  no equivalent of AArch64's PSTATE.DIT). The model has only the 32-bit
  `mul`, which T. Pornin's survey ("Constant-Time Mul", BearSSL) reports as
  constant time on the ARMv7 cores, including the Cortex-M3 (one cycle), which
  runs the same Thumb code (`target_arch = "arm"` includes ARMv7-M), and
  `mla`, its multiply-accumulate on the same multiplier, which the Cortex-M3
  Technical Reference Manual (ARM DDI 0337H, Table 3-1, "Cortex-M3
  instruction set summary") lists at a fixed two cycles; the long multiplies
  `umull`/`umlal` are left out, as the Cortex-M3 terminates them early
  depending on the operands (the same table: 3 to 5 and 4 to 7 cycles, its
  note a: "UMULL, SMULL, UMLAL, and SMLAL instructions use early termination
  depending on the size of the source values").
  The long multiply-accumulate `umaal` is modelled outside the baseline: it
  needs the CPU feature `umaal` (`Instr.requires`), which stands for an
  A-profile core (ARMv7-A, or ARMv8-A in AArch32). The Cortex-M3 does not
  have `UMAAL` (ARMv7-M has it only with the DSP extension, ARMv7E-M: DDI
  0403E, A7.7 "UMAAL"). On the A-profile cores the long multiplies take a
  time independent of their operands: Pornin's survey lists the 32×32→64
  multiply `umull` as constant time on the Cortex-A cores (in A32), and the
  Cortex-A72 Software Optimization Guide (ARM UAN 0016A, §3.5, "Divide and
  Multiply Instructions") gives `UMAAL` a fixed latency of 4 cycles (2 for
  the accumulate) and a throughput of one every two cycles, noting
  operand-dependent early termination for `SDIV` and `UDIV` alone. The
  emitter compiles code that needs it only where the printer's `featureCfg`
  allows (operating systems that run on A-profile cores alone), and
  `src/cpu.rs` may report it only there, so no code with `umaal` reaches a
  Cortex-M core.
* Calls are `bl` and returns `bx lr` (DDI 0406C, A8.8.25 "BL, BLX
  (immediate)", A8.8.27 "BX"). The return addresses are the next of the
  state's `unknowns`, which nothing constrains (see `TCB/Code.lean`); a
  return address also says whether the caller is ARM or Thumb code, which
  `bx` switches back to. A linker veneer between a `bl` and its target may
  change `r12` and the condition flags (AAELF32 §5.6.1.4, "Call and Jump
  relocations"), so a call leaves unknown values in them too.
* A `static` the code reads (`Artifact.consts`) is at the address
  `State.syms name`, where `name` is its name, which `adrSym` (`movw`,
  `movt` and an `add` of `pc`, resolved by the linker) puts in a register.
  No instruction changes `syms`: a static's address is fixed for the run of
  the program. `adrSym` reads `pc`, which is not otherwise an operand.
-/

@[expose] public section

namespace VG.Arm

inductive Reg
  | r0 | r1 | r2 | r3 | r4 | r5 | r6 | r7 | r8 | r9 | r10 | r11 | r12 | lr
  deriving DecidableEq, Repr, Inhabited

structure State where
  gpr : Reg → BitVec 32
  sp : BitVec 32
  /-- The N, Z, C and V flags. -/
  n : Bool
  z : Bool
  c : Bool
  v : Bool
  mem : Mem
  /-- Regions the code may read (in addition to `wr`). -/
  rd : List Region
  /-- Regions the code may read and write. -/
  wr : List Region
  /-- Values the model does not know, used in order: the return address each
  call stores and, on the ARM targets, what a linker veneer may leave in the
  intra-procedure-call scratch registers and condition flags (see
  `TCB/Code.lean`). -/
  unknowns : Nat → BitVec 32 := fun _ => 0
  /-- The address of each `static` the code can name (`adrSym`), by name. -/
  syms : String → BitVec 32 := fun _ => 0

inductive Shift | lsl | lsr | ror
  deriving DecidableEq, Repr

/-- The second operand of a data-processing instruction. -/
inductive Op2
  /-- `#imm` -/
  | imm (v : BitVec 32)
  /-- `rm` -/
  | reg (r : Reg)
  /-- `rm, <shift> #amount` -/
  | shifted (r : Reg) (sh : Shift) (amount : Nat)
  deriving DecidableEq, Repr

inductive DpOp | add | sub | and | orr | eor | bic
  deriving DecidableEq, Repr

inductive Instr
  /-- `mov d, op2` (with a shifted register, printed as the `lsl`/`lsr`/`ror`
  alias) -/
  | mov (d : Reg) (op2 : Op2)
  /-- `mvn d, op2` (bitwise NOT, no flags set). -/
  | mvn (d : Reg) (op2 : Op2)
  /-- `add`/`sub`/`and`/`orr`/`eor`/`bic d, n, op2` (no flags set) -/
  | dp (op : DpOp) (d n : Reg) (op2 : Op2)
  /-- `adds d, n, op2` (sets N, Z, C, V) -/
  | adds (d n : Reg) (op2 : Op2)
  /-- `adc d, n, op2` (adds the C flag; no flags set) -/
  | adc (d n : Reg) (op2 : Op2)
  /-- `subs d, n, op2` (sets N, Z, C, V) -/
  | subs (d n : Reg) (op2 : Op2)
  /-- `cmp n, op2` (sets N, Z, C, V) -/
  | cmp (n : Reg) (op2 : Op2)
  /-- `movw d, #imm16` -/
  | movw (d : Reg) (imm : BitVec 16)
  /-- `movt d, #imm16` -/
  | movt (d : Reg) (imm : BitVec 16)
  /-- `movw d, #:lower16:(name - L)`, `movt d, #:upper16:(name - L)`, then
  `add d, pc` (MOVW, MOVT, ADD (register)), `L` the value the `add` reads
  from `pc`: the address of the `static` `name`, `State.syms name`. -/
  | adrSym (d : Reg) (name : String)
  /-- `rev d, m` -/
  | rev (d m : Reg)
  /-- `mul d, n, m`: the low 32 bits of `n * m` (no flags set) -/
  | mul (d n m : Reg)
  /-- `mla d, n, m, a`: the low 32 bits of `n * m + a` (no flags set) -/
  | mla (d n m a : Reg)
  /-- `umaal lo, hi, n, m`: `hi:lo := n * m + hi + lo`, unsigned and 64 bits
  wide (no flags set; `lo` and `hi` distinct) -/
  | umaal (lo hi n m : Reg)
  /-- `ldr t, [n, #off]` (`0 ≤ off < 4096`) -/
  | ldr (t n : Reg) (off : Nat)
  /-- `str t, [n, #off]` (`0 ≤ off < 4096`) -/
  | str (t n : Reg) (off : Nat)
  /-- `ldrb t, [n, #off]` (`0 ≤ off < 4096`) -/
  | ldrb (t n : Reg) (off : Nat)
  /-- `strb t, [n, #off]` (`0 ≤ off < 4096`) -/
  | strb (t n : Reg) (off : Nat)
  /-- `ldr t, [sp, #off]` (`0 ≤ off < 4096`) -/
  | ldrSp (t : Reg) (off : Nat)
  /-- Non-flag-setting `add d, sp, #imm`, with an unrotated 8-bit immediate. -/
  | addSp (d : Reg) (imm : Nat)
  /-- `sub sp, sp, #bytes`, opening an 8-byte-aligned buffer frame (`bytes` an
  encodable immediate below 4096). -/
  | alloc (bytes : Nat)
  /-- `add sp, sp, #bytes`, releasing that buffer frame. -/
  | free (bytes : Nat)
  /-- `push {rs}`: the push of a frame (see `push`); `rs` must be in
  ascending order and not empty -/
  | push (rs : List Reg)
  /-- `ldr t, [sp], #n`: the pop of a frame of `n` bytes (see `pop`), `n` a
  multiple of 4 below 256 -/
  | pop (t : Reg) (n : Nat)
  deriving DecidableEq, Repr

/-- Branch conditions (`b<cond>`). -/
inductive Cond
  /-- `eq`: Z = 1 -/
  | eq
  /-- `ne`: Z = 0 -/
  | ne
  deriving DecidableEq, Repr

/-- The register number (`lr` is `r14`). -/
def Reg.num : Reg → Nat
  | .r0 => 0 | .r1 => 1 | .r2 => 2 | .r3 => 3 | .r4 => 4 | .r5 => 5 | .r6 => 6 | .r7 => 7
  | .r8 => 8 | .r9 => 9 | .r10 => 10 | .r11 => 11 | .r12 => 12 | .lr => 14

/-- A register list of `push` or `pop`: not empty, in ascending order (so
the printed list is the set of registers the instruction encodes, in the
order it accesses them). -/
def regList : List Reg → Bool
  | [] => false
  | [_] => true
  | r :: r' :: rs => r.num < r'.num && regList (r' :: rs)

/-- DDI 0406C A5.2.4, "Modified immediate constants in ARM instructions": an
8-bit value rotated right by an even amount. -/
def encodable (v : BitVec 32) : Bool :=
  (List.range 16).any fun k => (v.rotateLeft (2 * k)).toNat < 256

namespace State

def setReg (s : State) (r : Reg) (x : BitVec 32) : State :=
  { s with gpr := fun r' => if r' = r then x else s.gpr r' }

/-- The 64-bit address of a 32-bit address. -/
def addr (a : BitVec 32) : Addr := a.setWidth 64

/-- Load 4 bytes, faulting if not permitted. The address need not be aligned
(see "Word loads and stores" above). -/
def load32 (s : State) (a : Addr) : Option (BitVec 32) :=
  if InRegions (s.rd ++ s.wr) a 4 then some (s.mem.readW a 32) else none

/-- Store 4 bytes, faulting if not permitted. The address need not be aligned
(see "Word loads and stores" above). -/
def store32 (s : State) (a : Addr) (x : BitVec 32) : Option State :=
  if InRegions s.wr a 4 then some { s with mem := s.mem.writeW a x } else none

/-- Load 1 byte, faulting if not permitted. -/
def load8 (s : State) (a : Addr) : Option (BitVec 8) :=
  if InRegions (s.rd ++ s.wr) a 1 then some (s.mem a) else none

/-- Store 1 byte, faulting if not permitted. -/
def store8 (s : State) (a : Addr) (x : BitVec 8) : Option State :=
  if InRegions s.wr a 1 then some { s with mem := s.mem.writeW a x } else none

end State

/-- The value of the second operand (DDI 0406C A8.4.3, `Shift_C`; the carry
out of the shifter is not modelled, as no modelled instruction uses it), or
`none` if it cannot be encoded. -/
def Op2.eval (s : State) : Op2 → Option (BitVec 32)
  | .imm v => if encodable v then some v else none
  | .reg r => some (s.gpr r)
  | .shifted r sh n =>
    if 1 ≤ n ∧ n ≤ 31 then
      some (match sh with
        | .lsl => s.gpr r <<< n
        | .lsr => s.gpr r >>> n
        | .ror => (s.gpr r).rotateRight n)
    else none

/-- The flags of `x + y` (DDI 0406C A2.2.1, `AddWithCarry(x, y, '0')`). -/
def addFlags (s : State) (x y : BitVec 32) : State :=
  let r := x + y
  { s with n := r.msb, z := r == 0, c := 2 ^ 32 ≤ x.toNat + y.toNat,
           v := x.msb == y.msb && r.msb != x.msb }

/-- The flags of `x - y` (DDI 0406C A2.2.1, `AddWithCarry(x, NOT(y), '1')`). -/
def subFlags (s : State) (x y : BitVec 32) : State :=
  let r := x - y
  { s with n := r.msb, z := r == 0, c := y.toNat ≤ x.toNat,
           v := x.msb != y.msb && r.msb != x.msb }

/-- `REV`: `result<31:24> = R[m]<7:0>` etc. (DDI 0406C A8.8.145). -/
def rev (a : BitVec 32) : BitVec 32 :=
  a.extractLsb' 0 8 ++ a.extractLsb' 8 8 ++ a.extractLsb' 16 8 ++ a.extractLsb' 24 8

/-- Semantics, transcribing DDI 0406C A8.8: "MOV (immediate)", "MOV
(register)", "LSL/LSR/ROR (immediate)" (the aliases of MOV with a shifted
register); "ADD/SUB/AND/ORR/EOR (immediate)", "(register)" (with `S` = 0,
so no flags); "ADD (immediate/register)" with `S` = 1: `R[d]` and N, Z,
C, V from `AddWithCarry(R[n], op2, '0')`; "ADC (immediate)" and "ADC
(register)" (A8.8.1, A8.8.2) with `S` = 0: `R[d]` from
`AddWithCarry(R[n], op2, APSR.C)`, flags unchanged; "SUB
(immediate/register)" with `S` = 1 and "CMP": N, Z, C, V
from `AddWithCarry(R[n], NOT(op2), '1')`; "MOVW" (`R[d] = ZeroExtend(imm16)`);
"MOVT" (`R[d]<31:16> = imm16`, the low half unchanged); "REV"; "LDR
(immediate)"/"STR (immediate)" with a positive offset and no writeback
(A8.8.63, A8.8.204), including "LDR (immediate)" with `n` = 13 (`sp`) for
arguments on the stack; "LDRB (immediate)" (A8.8.68: `R[t] =
ZeroExtend(MemU[address,1], 32)`) and "STRB (immediate)" (A8.8.207:
`MemU[address,1] = R[t]<7:0>`) with a positive offset and no writeback;
"MUL" (A8.8.114) with `S` = 0: `result = operand1 * operand2; R[d] =
result<31:0>`, flags unchanged, where the operands are `SInt(R[n])` and
`SInt(R[m])` (the low 32 bits of the product are those of the unsigned
product). It exists in the ARM (encoding A1) and Thumb (encoding T2, ARMv6T2
and later; the 16-bit T1 encoding sets the flags outside an IT block, so an
assembler uses T2 for `mul`) instruction sets. `pc` (and, in Thumb, `sp`) as
any of the registers is UNPREDICTABLE, which the model cannot express; since
ARMv6, `d` may be `n` (the ARM encoding's `ArchVersion() < 6 && d == n`
restriction does not apply to ARMv7);
"MLA" (A8.8.100) with `S` = 0: `result = operand1 * operand2 + addend;
R[d] = result<31:0>`, flags unchanged, where the operands are `SInt(R[n])`
and `SInt(R[m])` and the addend `SInt(R[a])` (the low 32 bits of the result
are those of the unsigned `R[n] * R[m] + R[a]`). It exists in the ARM
(encoding A1) and Thumb (encoding T1, ARMv6T2 and later) instruction sets,
and so in the ARMv7 baseline: `requires` stays empty. `pc` (and, in Thumb,
`sp`) as any of the registers is UNPREDICTABLE, which the model cannot
express (T1 with `Ra` = `pc` is MUL's encoding); the ARM encoding's
`ArchVersion() < 6 && d == n` restriction does not apply to ARMv7.

"UMAAL" (DDI 0406C A8.8, "UMAAL"): `result =
UInt(R[n]) * UInt(R[m]) + UInt(R[dHi]) + UInt(R[dLo]); R[dHi] =
result<63:32>; R[dLo] = result<31:0>`, flags unchanged. The sum is below
`2^64` (`(2^32 - 1)^2 + 2 (2^32 - 1) = 2^64 - 1`). It exists in the ARM
(encoding A1, ARMv6 and later) and Thumb (encoding T1, ARMv6T2 and later,
and ARMv7E-M) instruction sets; `dHi = dLo` is UNPREDICTABLE, which the
model makes a fault, and `pc` (and, in Thumb, `sp`) as any of the registers
is UNPREDICTABLE, which the model cannot express. It requires the feature
`umaal` (see "Instructions whose timing depends on their operands" above).

`adrSym d name` is three instructions, which the linker completes with the
static's address `S` (`State.syms name`): "MOVW" (A8.8.102, "MOV
(immediate)" encoding A2 or T3: `R[d] = ZeroExtend(imm16, 32)`), then "MOVT"
(A8.8.106, encoding A1 or T1: `R[d]<31:16> = imm16`), then `add d, pc`,
"ADD (register, ARM)" (A8.8.7, encoding A1, `add d, d, pc`) or "ADD
(register, Thumb)" (A8.8.6, the 16-bit encoding T2), with `S` = 0 and `m` =
15: `R[d] = R[d] + R[15]`, no flags set. Their immediates are bits 15:0 and
31:16 of `S - L`, where `L` is the value the `add` reads from `pc`: its
address plus 8 in ARM state and plus 4 in Thumb state (A2.3, "ARM core
registers"), so its address plus twice its size (A1 is 4 bytes, T2 2),
which the printed relocation expression says in either state. The relocations are
`R_ARM_MOVW_PREL_NC` and `R_ARM_MOVT_PREL` in ARM code and
`R_ARM_THM_MOVW_PREL_NC` and `R_ARM_THM_MOVT_PREL` in Thumb code (ELF for
the Arm Architecture, AAELF32 §5.6.1, "Static Data relocations": `((S + A) |
T) - P` and `(S + A) - P`, `T` = 0 for the data object a `static` is, the
addend `A` making the difference relative to `L`; MOVT takes bits 31:16 of
the result), so `R[d] = (S - L) + L = S`, modulo 2³², whatever the distance
from the code to the static. The relocations are PC-relative, so the code
is position independent, as Rust's PIC executables and shared libraries
require (the absolute `R_ARM_MOVW_ABS_NC` would not link there).
https://github.com/ARM-software/abi-aa/blob/2025Q4/aaelf32/aaelf32.rst.
`d` is never `sp` or `pc` (UNPREDICTABLE in the T3, T1 encodings of MOVW and
MOVT, `BadReg(d)`, and a branch in ADD's); `lr` is allowed. MOVW and MOVT
are ARMv6T2 and later, in both instruction sets, and so in the ARMv7
baseline: `requires` stays empty. All three take a time independent of
their operands.

`MVN` and `BIC` follow Arm's instruction pseudocode, with `setflags`
false: `result = NOT(shifted)` and `result = R[n] AND NOT(shifted)` (the
immediate forms use `imm32` instead). The existing `Op2.eval` implements
that operand's immediate expansion and immediate shift. `Reg` excludes
PC and SP, so none of the PC-write or exception-return cases apply. These
are baseline ARMv7-A instructions in both A32 and T32, with no memory
accesses and no NZCV changes. Sources: Arm ARM DDI 0406C, "MVN (immediate)",
"MVN (register)", "BIC (immediate)" and "BIC (register)"; Arm's A32/T32
instruction pseudocode v2023-06, mirrored at:
https://mikhailarkhipov.github.io/ARM-doc/A32/mvn_i.html
https://mikhailarkhipov.github.io/ARM-doc/A32/mvn_r.html
https://mikhailarkhipov.github.io/ARM-doc/A32/bic_i.html
https://mikhailarkhipov.github.io/ARM-doc/A32/bic_r.html -/
def exec : Instr → State → Option State
  | .mov d op2, s => (op2.eval s).map fun x => s.setReg d x
  | .mvn d op2, s => (op2.eval s).map fun x => s.setReg d (~~~x)
  | .dp op d n op2, s => (op2.eval s).map fun y =>
    let x := s.gpr n
    s.setReg d (match op with
      | .add => x + y | .sub => x - y | .and => x &&& y | .orr => x ||| y | .eor => x ^^^ y | .bic => x &&& ~~~y)
  | .adds d n op2, s => (op2.eval s).map fun y =>
    (addFlags s (s.gpr n) y).setReg d (s.gpr n + y)
  | .adc d n op2, s => (op2.eval s).map fun y =>
    s.setReg d (s.gpr n + y + (if s.c then 1 else 0))
  | .subs d n op2, s => (op2.eval s).map fun y =>
    (subFlags s (s.gpr n) y).setReg d (s.gpr n - y)
  | .cmp n op2, s => (op2.eval s).map fun y => subFlags s (s.gpr n) y
  | .movw d imm, s => some (s.setReg d (imm.setWidth 32))
  | .movt d imm, s => some (s.setReg d (imm ++ (s.gpr d).extractLsb' 0 16 : BitVec 32))
  | .adrSym d name, s => some (s.setReg d (s.syms name))
  | .rev d m, s => some (s.setReg d (rev (s.gpr m)))
  | .mul d n m, s => some (s.setReg d (s.gpr n * s.gpr m))
  | .mla d n m a, s => some (s.setReg d (s.gpr n * s.gpr m + s.gpr a))
  | .umaal lo hi n m, s =>
    if lo = hi then none else
      let r := (s.gpr n).toNat * (s.gpr m).toNat + (s.gpr hi).toNat + (s.gpr lo).toNat
      some ((s.setReg lo (BitVec.ofNat 32 r)).setReg hi (BitVec.ofNat 32 (r / 2 ^ 32)))
  | .ldr t n off, s =>
    if off < 4096 then
      (s.load32 (State.addr (s.gpr n + BitVec.ofNat 32 off))).map fun x => s.setReg t x
    else none
  | .str t n off, s =>
    if off < 4096 then s.store32 (State.addr (s.gpr n + BitVec.ofNat 32 off)) (s.gpr t)
    else none
  | .ldrb t n off, s =>
    if off < 4096 then
      (s.load8 (State.addr (s.gpr n + BitVec.ofNat 32 off))).map fun x => s.setReg t (x.setWidth 32)
    else none
  | .strb t n off, s =>
    if off < 4096 then s.store8 (State.addr (s.gpr n + BitVec.ofNat 32 off)) ((s.gpr t).setWidth 8)
    else none
  | .ldrSp t off, s =>
    if off < 4096 then
      (s.load32 (State.addr (s.sp + BitVec.ofNat 32 off))).map fun x => s.setReg t x
    else none
  | .addSp d imm, s =>
    if imm < 256 then some (s.setReg d (s.sp + BitVec.ofNat 32 imm)) else none
  -- Frame delimiters run only through `push` and `pop`.
  | .push _, _ | .pop .., _ | .alloc _, _ | .free _, _ => none

/-- The addresses of `n` consecutive words from `a`. -/
def words (a : BitVec 32) (n : Nat) : List Addr :=
  (List.range n).map fun i => State.addr (a + BitVec.ofNat 32 (4 * i))

def addrs : Instr → State → List Addr
  | .ldr _ n off, s => [State.addr (s.gpr n + BitVec.ofNat 32 off)]
  | .str _ n off, s => [State.addr (s.gpr n + BitVec.ofNat 32 off)]
  | .ldrb _ n off, s => [State.addr (s.gpr n + BitVec.ofNat 32 off)]
  | .strb _ n off, s => [State.addr (s.gpr n + BitVec.ofNat 32 off)]
  | .ldrSp _ off, s => [State.addr (s.sp + BitVec.ofNat 32 off)]
  | .push rs, s => words (s.sp - BitVec.ofNat 32 (4 * rs.length)) rs.length
  | .pop .., s => [State.addr s.sp]
  | _, _ => []

def eval : Cond → State → Option Bool
  | .eq, s => some s.z
  | .ne, s => some !s.z

/-- DDI 0406C, A8.8.25 "BL, BLX (immediate)": `LR = PC − 4` in ARM state,
`LR = PC<31:1> : '1'` in Thumb state (the address of the next instruction,
and which state it is in), then the branch (with a change of instruction set
to that of the target, which the linker arranges), possibly through a linker
veneer, which may change `r12` and the condition flags (AAELF32 §5.6.1.4,
"Call and Jump relocations":
https://github.com/ARM-software/abi-aa/blob/2025Q4/aaelf32/aaelf32.rst).
The next three unknown words supply the return address, `r12`, and four
independent flag bits. Nothing constrains or makes these unknowns public. -/
def call (s : State) : Option State :=
  some { (s.setReg .lr (s.unknowns 0)).setReg .r12 (s.unknowns 1) with
    n := (s.unknowns 2).getLsbD 0
    z := (s.unknowns 2).getLsbD 1
    c := (s.unknowns 2).getLsbD 2
    v := (s.unknowns 2).getLsbD 3
    unknowns := fun n => s.unknowns (n + 3) }

/-- DDI 0406C, A8.8.27 "BX" (`bx lr`): `BXWritePC(R[14])`, a branch to the
address in `lr`, in the instruction set its bit 0 selects. It returns after
the call instruction if `lr` is the return address the call left (`s₁`);
otherwise the model faults. -/
def ret (s₁ s₂ : State) : Option State :=
  if s₂.gpr .lr = s₁.gpr .lr then some s₂ else none

/-- Store the words `vs` at consecutive addresses from `a`. -/
def storeWords (m : Mem) (a : BitVec 32) : List (BitVec 32) → Mem
  | [] => m
  | v :: vs => storeWords (m.writeW (State.addr a) v) (a + 4) vs

/-! Arm DDI 0597 (2024-06), "ADD, ADDS (SP plus immediate)" (pp. 29–31)
and "SUB, SUBS (SP minus immediate)" (pp. 536–537): non-flag-setting
addition/subtraction from R[13], with the result written to R[d].
https://documentation-service.arm.com/static/668bf4af69e89f01e39c4cd2

The immediates of `addSp` are below 256, encodable without rotation in A32
and with T32 modified immediates. Those of `alloc` and `free`, the frame's
size, are below 4096 and A32 modified immediates (`encodable`): T32 encodes
every such value (`SUBW`/`ADDW`, encoding T3, a 12-bit immediate), so the
assembler picks an encoding of the same meaning in either instruction set.
All of these forms are baseline ARMv7/Thumb-2; no optional CPU feature is
required. Frame sizes must be positive multiples of 8, preserving the ABI's
alignment, and less than a page, so that an allocation does not move SP past
a guard page below the stack. Allocation cannot underflow and grants one
contiguous region without initializing memory. Release requires the exact
region and unchanged SP and permissions. Neither changes flags or memory.
-/

/-- The push of a frame, DDI 0406C A8.8.133 "PUSH" (= `STMDB sp!`):
`address = SP - 4*BitCount(registers)`; for each register in ascending
order, `MemA[address,4] = R[i]; address = address + 4`; `SP = SP -
4*BitCount(registers)`. The frame becomes a writable region, at the head of
`wr`. Faults if the register list is not valid (`regList`) or the frame
would wrap around the address space. -/
def push : Instr → State → Option State
  | .alloc bytes, s =>
    if 0 < bytes ∧ bytes < 4096 ∧ bytes % 8 = 0 ∧ encodable (BitVec.ofNat 32 bytes) ∧
        bytes ≤ s.sp.toNat then
      let sp := s.sp - BitVec.ofNat 32 bytes
      some { s with sp := sp, wr := ⟨State.addr sp, bytes⟩ :: s.wr }
    else none
  | .push rs, s =>
    let n := 4 * rs.length
    if regList rs ∧ n ≤ s.sp.toNat then
      let sp := s.sp - BitVec.ofNat 32 n
      some { s with
        sp := sp
        mem := storeWords s.mem sp (rs.map s.gpr)
        wr := ⟨State.addr sp, n⟩ :: s.wr }
    else none
  | _, _ => none

/-- The pop of a frame, DDI 0406C A8.8.63 "LDR (immediate, ARM)" and A8.8.62
"LDR (immediate, Thumb)" (encoding T4, whose offset is below 256),
post-indexed (`ldr t, [sp], #n`): `address = R[n]; data =
MemU[address,4]; R[n] = R[n] + imm32; R[t] = data`, with `n` = 13 (`sp`).
Faults unless `n` is a multiple of 4 below 256, the stack pointer and the
writable regions are those the push left (`s₁`), and the frame, the region
at their head, has `n` bytes; it removes the frame. -/
def pop : Instr → State → State → Option State
  | .free bytes, s₁, s₂ =>
    if 0 < bytes ∧ bytes < 4096 ∧ bytes % 8 = 0 ∧ encodable (BitVec.ofNat 32 bytes) ∧
        s₂.sp = s₁.sp ∧ s₂.wr = s₁.wr ∧ s₁.wr.head? = some ⟨State.addr s₁.sp, bytes⟩ then
      some { s₂ with sp := s₂.sp + BitVec.ofNat 32 bytes, wr := s₂.wr.tail }
    else none
  | .pop t n, s₁, s₂ =>
    if n % 4 = 0 ∧ n < 256 ∧ s₂.sp = s₁.sp ∧ s₂.wr = s₁.wr ∧
        s₁.wr.head? = some ⟨State.addr s₁.sp, n⟩ then
      some { s₂.setReg t (s₂.mem.readW (State.addr s₂.sp) 32) with
        sp := s₂.sp + BitVec.ofNat 32 n, wr := s₂.wr.tail }
    else none
  | _, _, _ => none

/-- The CPU features an instruction needs beyond the ARMv7 baseline: `umaal`
for UMAAL, which the Cortex-M3 lacks (see "Instructions whose timing depends
on their operands" above); every other modelled instruction is in the
baseline. -/
def Instr.requires : Instr → List String
  | .umaal .. => ["umaal"]
  | _ => []

abbrev isa : ISA where
  State := State
  Instr := Instr
  Cond := Cond
  exec := exec
  addrs := addrs
  eval := eval
  call := call
  callAddrs _ := []
  ret := ret
  retAddrs _ := []
  -- No modelled instruction writes the stack pointer, other than the push
  -- and pop of a frame.
  writesSp _ := false
  push := push
  pop := pop
  requires := Instr.requires

end VG.Arm
