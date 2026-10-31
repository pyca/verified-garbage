module

public import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# Machine code of the 64-bit RISC-V model's instructions

**Trusted.** The 32-bit encoding of each straight-line instruction of the
model (`Instr`), and of the return: what the printer (`Print.lean`) emits,
as `.insn 4, <word>`, in place of the instruction's text, so that what runs
is these words, not the assembler's reading of a mnemonic. Branches, jumps,
calls and `lla`, whose bytes depend on where their target is, are still
printed as text for the assembler and linker to lay out.

The encodings are The RISC-V Instruction Set Manual, Volume I: Unprivileged
Architecture (Version 20250508), chapter "RV32I Base Integer Instruction
Set", sections "Base Instruction Formats" (the R-, I-, S- and U-type
layouts below), "Integer Computational Instructions", "Load and Store
Instructions" and "Unconditional Jumps" (`jalr`); chapter "RV64I Base Integer
Instruction Set" (the doubleword loads and stores, `lwu`, the `*w` forms and
the 6-bit shift amounts of `slli`/`srli`/`srai`); chapter "M Extension for
Integer Multiplication and Division" (`mul`, `mulhu`); and the opcodes and
`funct3`/`funct7` of each in the chapter "RV32/64G Instruction Set
Listings". Each is the base (32-bit) instruction the model's semantics
describes: never a compressed (C) encoding, so the code also runs on CPUs
without the C extension.

`encode` is `none` for an instruction whose operand does not fit its field
(e.g. an `addi` immediate outside `-2048 ≤ imm < 2048`), which the printer
reports as unencodable (`Printer.unencodable`) and the emitter refuses
(`Rust.checkEncodable`), rather than truncating it; and for `lla`, which is
printed as text (`Printer.symLines`).
-/

@[expose] public section

namespace VG.RISCV64

/-- The number `n` of the register `xn` (psABI, "Integer Register
Convention": `ra` is `x1`, `t0`–`t2` are `x5`–`x7`, `s0`–`s1` are `x8`–`x9`,
`a0`–`a7` are `x10`–`x17`, `s2`–`s11` are `x18`–`x27`, `t3`–`t6` are
`x28`–`x31`). -/
def Reg.num : Reg → Nat
  | .ra => 1 | .t0 => 5 | .t1 => 6 | .t2 => 7 | .s0 => 8 | .s1 => 9
  | .a0 => 10 | .a1 => 11 | .a2 => 12 | .a3 => 13 | .a4 => 14 | .a5 => 15
  | .a6 => 16 | .a7 => 17 | .s2 => 18 | .s3 => 19 | .s4 => 20 | .s5 => 21
  | .s6 => 22 | .s7 => 23 | .s8 => 24 | .s9 => 25 | .s10 => 26 | .s11 => 27
  | .t3 => 28 | .t4 => 29 | .t5 => 30 | .t6 => 31

namespace Enc

/-- `x0` (`zero`) and `x2` (`sp`), which are not registers of the model. -/
def zero : Nat := 0
def sp : Nat := 2

/-- The major opcodes (bits 6–0), "RV32/64G Instruction Set Listings". -/
def opLoad : Nat := 0x03
def opImm : Nat := 0x13
def opImm32 : Nat := 0x1b
def opStore : Nat := 0x23
def opReg : Nat := 0x33
def opLui : Nat := 0x37
def opReg32 : Nat := 0x3b
def opJalr : Nat := 0x67

/-- R-type: `funct7` (31–25), `rs2` (24–20), `rs1` (19–15), `funct3`
(14–12), `rd` (11–7), opcode (6–0). -/
def r (funct7 funct3 opcode rd rs1 rs2 : Nat) : Nat :=
  funct7 <<< 25 ||| rs2 <<< 20 ||| rs1 <<< 15 ||| funct3 <<< 12 ||| rd <<< 7 ||| opcode

/-- Whether `imm` fits a 12-bit signed immediate (the model's `imm12`). -/
def fits12 (imm : Int) : Bool := -2048 ≤ imm && imm < 2048

/-- The 12 bits of `imm` (two's complement), for `fits12 imm`. -/
def bits12 (imm : Int) : Nat := (imm % 4096).toNat

/-- I-type: `imm[11:0]` (31–20), `rs1`, `funct3`, `rd`, opcode; `none` if
`imm` does not fit. -/
def i (imm : Int) (funct3 opcode rd rs1 : Nat) : Option Nat :=
  if fits12 imm then
    some (bits12 imm <<< 20 ||| rs1 <<< 15 ||| funct3 <<< 12 ||| rd <<< 7 ||| opcode)
  else none

/-- S-type: `imm[11:5]` (31–25), `rs2`, `rs1`, `funct3`, `imm[4:0]` (11–7),
opcode; `none` if `imm` does not fit. -/
def s (imm : Int) (funct3 opcode rs1 rs2 : Nat) : Option Nat :=
  if fits12 imm then
    let u := bits12 imm
    some ((u >>> 5) <<< 25 ||| rs2 <<< 20 ||| rs1 <<< 15 ||| funct3 <<< 12 |||
      (u % 32) <<< 7 ||| opcode)
  else none

/-- U-type: `imm[31:12]` (31–12), `rd`, opcode. -/
def u (imm20 : Nat) (opcode rd : Nat) : Nat := imm20 <<< 12 ||| rd <<< 7 ||| opcode

/-- `addi rd, rs1, imm` ("Integer Register-Immediate Instructions":
`OP-IMM`, `funct3` 0). -/
def addi (rd rs1 : Nat) (imm : Int) : Option Nat := i imm 0 opImm rd rs1

/-- `funct3` of `and`/`or`/`xor` and of `andi`/`ori`/`xori`. -/
def logicFunct3 : LogicOp → Nat
  | .and => 7 | .or => 6 | .xor => 4

/-- `funct3` of a zero-extending load (`lbu`, `lhu`, `lwu`, `ld`; `LOAD`). -/
def loadFunct3 : Width → Nat
  | .b => 4 | .h => 5 | .w => 6 | .d => 3

/-- `funct3` of a store (`sb`, `sh`, `sw`, `sd`; `STORE`). -/
def storeFunct3 : Width → Nat
  | .b => 0 | .h => 1 | .w => 2 | .d => 3

/-- `funct3` of a shift by an immediate: 1 for `slli`/`slliw`, 5 for
`srli`/`srai` and `srliw`/`sraiw`. -/
def shiftFunct3 : ShiftOp → Nat
  | .sll => 1 | .srl => 5 | .sra => 5

/-- Bit 30 of an arithmetic shift right by an immediate (`srai`, `sraiw`),
0 for the logical ones: "the right shift type is encoded in bit 30". -/
def shiftBit30 : ShiftOp → Nat
  | .sra => 1 <<< 30 | _ => 0

/-- `ld rd, off(rs1)` and `sd rs2, off(rs1)`, for a frame's push and pop. -/
def ld (rd rs1 : Nat) (off : Int) : Option Nat := i off (loadFunct3 .d) opLoad rd rs1
def sd (rs2 rs1 : Nat) (off : Int) : Option Nat := s off (storeFunct3 .d) opStore rs1 rs2

end Enc

/-- The words of an instruction, in order: one for each base instruction it
stands for, the instructions `Instr.asm` (`Print.lean`) names; `none` if an
operand does not fit its field (see the module docs), or for `lla`. -/
def Instr.encode : Instr → Option (List Nat)
  | .add d n m => some [Enc.r 0 0 Enc.opReg d.num n.num m.num]
  | .sub d n m => some [Enc.r 0x20 0 Enc.opReg d.num n.num m.num]
  | .addw d n m => some [Enc.r 0 0 Enc.opReg32 d.num n.num m.num]
  | .subw d n m => some [Enc.r 0x20 0 Enc.opReg32 d.num n.num m.num]
  | .sltu d n m => some [Enc.r 0 3 Enc.opReg d.num n.num m.num]
  | .mul d n m => some [Enc.r 1 0 Enc.opReg d.num n.num m.num]
  | .mulhu d n m => some [Enc.r 1 3 Enc.opReg d.num n.num m.num]
  | .logic op d n m => some [Enc.r 0 (Enc.logicFunct3 op) Enc.opReg d.num n.num m.num]
  | .addi d n imm => (Enc.addi d.num n.num imm).map ([·])
  | .addiw d n imm => (Enc.i imm 0 Enc.opImm32 d.num n.num).map ([·])
  | .logicImm op d n imm => (Enc.i imm (Enc.logicFunct3 op) Enc.opImm d.num n.num).map ([·])
  | .li d imm => (Enc.addi d.num Enc.zero imm).map ([·])
  | .lui d imm => some [Enc.u imm.toNat Enc.opLui d.num]
  | .shift op .d d n sh =>
    if sh < 64 then
      some [Enc.shiftBit30 op ||| sh <<< 20 ||| n.num <<< 15 ||| Enc.shiftFunct3 op <<< 12 |||
        d.num <<< 7 ||| Enc.opImm]
    else none
  | .shift op .w d n sh =>
    if sh < 32 then
      some [Enc.shiftBit30 op ||| sh <<< 20 ||| n.num <<< 15 ||| Enc.shiftFunct3 op <<< 12 |||
        d.num <<< 7 ||| Enc.opImm32]
    else none
  | .load wd t n off =>
    if off < 2048 then (Enc.i off (Enc.loadFunct3 wd) Enc.opLoad t.num n.num).map ([·]) else none
  | .store wd t n off =>
    if off < 2048 then (Enc.s off (Enc.storeFunct3 wd) Enc.opStore n.num t.num).map ([·]) else none
  | .push r => do
    let a ← Enc.addi Enc.sp Enc.sp (-16)
    let b ← Enc.sd r.num Enc.sp 8
    return [a, b]
  | .pop r => do
    let a ← Enc.ld r.num Enc.sp 8
    let b ← Enc.addi Enc.sp Enc.sp 16
    return [a, b]
  | .alloc bytes =>
    if bytes < 2048 then (Enc.addi Enc.sp Enc.sp (-(bytes : Int))).map ([·])
    else do
      let a ← Enc.addi Enc.sp Enc.sp (-2032)
      let b ← Enc.addi Enc.sp Enc.sp (-((bytes - 2032 : Nat) : Int))
      return [a, b]
  | .free bytes =>
    if bytes < 2048 then (Enc.addi Enc.sp Enc.sp bytes).map ([·])
    else do
      let a ← Enc.addi Enc.sp Enc.sp ((bytes - 2032 : Nat) : Int)
      let b ← Enc.addi Enc.sp Enc.sp 2032
      return [a, b]
  | .addSp d imm => if imm < 2048 then (Enc.addi d.num Enc.sp imm).map ([·]) else none
  | .lla _ _ => none

/-- `ret`, `jalr x0, 0(ra)` ("Unconditional Jumps": `JALR`, `funct3` 0). -/
def retWord : Nat :=
  Enc.i 0 0 Enc.opJalr Enc.zero Reg.ra.num |>.getD 0

/-- `w` as 8 hexadecimal digits, after `0x`. -/
def hex32 (w : Nat) : String :=
  let ds := Nat.toDigits 16 (w % 2 ^ 32)
  "0x" ++ String.ofList (List.replicate (8 - ds.length) '0' ++ ds)

/-- The assembler directive emitting the 32-bit instruction `w` (RISC-V
Assembly Programmer's Manual, ".insn": `.insn <length>, <value>` emits
`value` as an instruction of `length` bytes). -/
def insnLine (w : Nat) : String := s!".insn 4, {hex32 w}"

end VG.RISCV64
