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
layouts below), "Integer Computational Instructions" (among them the
register-register shifts `sll`, `srl`, `sra`, `sllw`, `srlw`, `sraw`), "Load and Store
Instructions" and "Unconditional Jumps" (`jalr`); chapter "RV64I Base Integer
Instruction Set" (the doubleword loads and stores, `lwu`, the `*w` forms and
the 6-bit shift amounts of `slli`/`srli`/`srai`); chapter "M Extension for
Integer Multiplication and Division" (`mul`, `mulhu`); and the opcodes and
`funct3`/`funct7` of each in the chapter "RV32/64G Instruction Set
Listings". Each is the base (32-bit) instruction the model's semantics
describes, which `compress` then replaces by its compressed (16-bit)
encoding when it has one (chapter "\"C\" Extension for Compressed
Instructions", whose every instruction "expands into a single 32-bit
instruction in the base ISA"), as the assembler would: the target requires
the C extension (`Target.lean`'s `rustCfg`).

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

/-- `funct3` of a shift: 1 for `slli`/`slliw` and `sll`/`sllw`, 5 for
`srli`/`srai`, `srliw`/`sraiw`, `srl`/`sra` and `srlw`/`sraw`. -/
def shiftFunct3 : ShiftOp → Nat
  | .sll => 1 | .srl => 5 | .sra => 5

/-- Bit 30 of an arithmetic shift right (`srai`, `sraiw`, and `sra`, `sraw`,
whose `funct7` is `0100000`), 0 for the logical ones: "the right shift type
is encoded in bit 30". -/
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
  | .shiftReg op .d d n m =>
    some [Enc.r (Enc.shiftBit30 op >>> 25) (Enc.shiftFunct3 op) Enc.opReg d.num n.num m.num]
  | .shiftReg op .w d n m =>
    some [Enc.r (Enc.shiftBit30 op >>> 25) (Enc.shiftFunct3 op) Enc.opReg32 d.num n.num m.num]
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

namespace C

/-- The 3-bit number of a register of the compressed formats' `rd'`,
`rs1'` and `rs2'` fields, `x8`–`x15` ("Compressed Instruction Formats",
"RVC Register Number"); `none` for any other. -/
def reg' (n : Nat) : Option Nat := if 8 ≤ n ∧ n ≤ 15 then some (n - 8) else none

/-- The 12-bit immediate `u` (two's complement) as an integer. -/
def sext12 (u : Nat) : Int := if u < 2048 then u else (u : Int) - 4096

/-- Whether `imm` fits a 6-bit signed immediate, and its 6 bits. -/
def fits6 (imm : Int) : Bool := -32 ≤ imm && imm < 32
def bits6 (imm : Int) : Nat := (imm % 64).toNat

/-- Bit `i` of `n`, at bit `j`. -/
def bit (n i j : Nat) : Nat := ((n >>> i) % 2) <<< j

/-- CI format: `funct3` (15–13), `imm[5]` (12), `rd`/`rs1` (11–7),
`imm[4:0]` (6–2), opcode (1–0). -/
def ci (funct3 op rd imm6 : Nat) : Nat :=
  funct3 <<< 13 ||| bit imm6 5 12 ||| rd <<< 7 ||| (imm6 % 32) <<< 2 ||| op

/-- CR format: `funct4` (15–12), `rd`/`rs1` (11–7), `rs2` (6–2), opcode. -/
def cr (funct4 op rd rs2 : Nat) : Nat := funct4 <<< 12 ||| rd <<< 7 ||| rs2 <<< 2 ||| op

/-- CA format: `funct6` (15–10), `rd'`/`rs1'` (9–7), `funct2` (6–5), `rs2'`
(4–2), opcode 01. -/
def ca (funct6 funct2 rd' rs2' : Nat) : Nat :=
  funct6 <<< 10 ||| rd' <<< 7 ||| funct2 <<< 5 ||| rs2' <<< 2 ||| 1

/-- `c.srli`, `c.srai` and `c.andi` (CB format, opcode 01, `funct3` 100):
`imm[5]` (12), `funct2` (11–10), `rd'` (9–7), `imm[4:0]` (6–2). -/
def cb (funct2 rd' imm6 : Nat) : Nat :=
  4 <<< 13 ||| bit imm6 5 12 ||| funct2 <<< 10 ||| rd' <<< 7 ||| (imm6 % 32) <<< 2 ||| 1

/-- `c.ld`/`c.sd` (CL/CS, opcode 00, `funct3` 011/111): `uimm[5:3]`
(12–10), `rs1'` (9–7), `uimm[7:6]` (6–5), `rd'`/`rs2'` (4–2). -/
def clsD (funct3 rs1' r' off : Nat) : Nat :=
  funct3 <<< 13 ||| ((off >>> 3) % 8) <<< 10 ||| rs1' <<< 7 ||| ((off >>> 6) % 4) <<< 5 ||| r' <<< 2

/-- `c.sw` (CS, opcode 00, `funct3` 110): `uimm[5:3]` (12–10), `rs1'`,
`uimm[2]` (6), `uimm[6]` (5), `rs2'`. -/
def csW (rs1' r' off : Nat) : Nat :=
  6 <<< 13 ||| ((off >>> 3) % 8) <<< 10 ||| rs1' <<< 7 ||| bit off 2 6 ||| bit off 6 5 ||| r' <<< 2

end C

open C in
/-- The compressed (16-bit) encoding of the 32-bit instruction `w`, if the
C extension has one: the one the assembler chooses (LLVM's `CompressPat`s,
`RISCVInstrInfoC.td`, which it tries in this order), as chapter "\"C\"
Extension for Compressed Instructions" defines each, by the base
instruction it expands to (RV64C):
* `addi`: `c.addi4spn rd', sp, nzuimm` (`nzuimm` a nonzero multiple of 4
  below 1024; "Integer Register-Immediate Operations"), `c.addi rd, nzimm`
  (`rd = rs1 ≠ x0`, nonzero `-32 ≤ nzimm < 32`), `c.li rd, imm` (`rs1 = x0`,
  `-32 ≤ imm < 32`), `c.addi16sp nzimm` (`rd = rs1 = sp`, a nonzero multiple
  of 16, `-512 ≤ nzimm < 512`), `c.mv rd, rs1` (`imm = 0`, "Integer
  Register-Register Operations");
* `addiw`: `c.addiw rd, imm` (`rd = rs1 ≠ x0`, `-32 ≤ imm < 32`);
* `andi`: `c.andi rd', imm` (`rd = rs1`, `-32 ≤ imm < 32`); `slli`:
  `c.slli rd, shamt` (`rd = rs1 ≠ x0`, `shamt ≠ 0`); `srli`/`srai`:
  `c.srli`/`c.srai rd', shamt` (`rd = rs1`, `shamt ≠ 0`);
* `lui`: `c.lui rd, nzimm` (`rd ∉ {x0, sp}`, `nzimm` a nonzero
  sign-extended 6-bit value);
* `add`: `c.add rd, rs2` (`rd = rs1`, or `rd = rs2` with the operands
  swapped, `rd`, `rs2 ≠ x0`); `sub`, `and`, `or`, `xor`, `addw`, `subw`:
  `c.sub`, `c.and`, `c.or`, `c.xor`, `c.addw`, `c.subw rd', rs2'`
  (`rd = rs1`, or for the commutative ones `rd = rs2` swapped);
* `ld`, `sd`: `c.ld`/`c.sd` (`x8`–`x15`, offset a multiple of 8 below 256),
  `c.ldsp`/`c.sdsp` (base `sp`, a multiple of 8 below 512, `c.ldsp`'s
  `rd ≠ x0`; "Stack-Pointer-Based Loads and Stores"); `sw`: `c.sw`
  (a multiple of 4 below 128), `c.swsp` (base `sp`, a multiple of 4 below
  256);
* `jalr x0, 0(rs1)`: `c.jr rs1` (`rs1 ≠ x0`; "Control Transfer
  Instructions").
The others (`sltu`, `mul`, `mulhu`, `ori`, `xori`, the `*w` shifts, the
shifts by a register, `lbu`, `lhu`, `lwu`, `sb`, `sh`) have none in RV64C. -/
def compress (w : Nat) : Option Nat :=
  let op := w % 128
  let rd := (w >>> 7) % 32
  let f3 := (w >>> 12) % 8
  let rs1 := (w >>> 15) % 32
  let rs2 := (w >>> 20) % 32
  let f7 := w >>> 25
  let immI := sext12 (w >>> 20)
  let immS := sext12 ((w >>> 25) <<< 5 ||| (w >>> 7) % 32)
  match op, f3 with
  | 0x13, 0 =>
    -- addi
    (match reg' rd with
      | some rd' =>
        if rs1 == 2 && 0 < immI && immI % 4 == 0 && immI < 1024 then
          let u := immI.toNat
          some (bit u 5 12 ||| bit u 4 11 ||| ((u >>> 6) % 16) <<< 7 ||| bit u 2 6 |||
            bit u 3 5 ||| rd' <<< 2)
        else none
      | none => none)
    <|> (if rd == rs1 && rd != 0 && immI != 0 && fits6 immI then some (ci 0 1 rd (bits6 immI))
      else none)
    <|> (if rs1 == 0 && rd != 0 && fits6 immI then some (ci 2 1 rd (bits6 immI)) else none)
    <|> (if rd == 2 && rs1 == 2 && immI != 0 && immI % 16 == 0 && -512 ≤ immI && immI < 512 then
        let u := (immI % 1024).toNat
        some (3 <<< 13 ||| bit u 9 12 ||| 2 <<< 7 ||| bit u 4 6 ||| bit u 6 5 |||
          ((u >>> 7) % 4) <<< 3 ||| bit u 5 2 ||| 1)
      else none)
    <|> (if immI == 0 && rd != 0 && rs1 != 0 then some (cr 8 2 rd rs1) else none)
  | 0x1b, 0 =>
    -- addiw
    if rd == rs1 && rd != 0 && fits6 immI then some (ci 1 1 rd (bits6 immI)) else none
  | 0x13, 7 =>
    -- andi
    match reg' rd with
    | some rd' => if rd == rs1 && fits6 immI then some (cb 2 rd' (bits6 immI)) else none
    | none => none
  | 0x13, 1 =>
    -- slli (`imm[11:6]` = 0)
    let sh := (w >>> 20) % 64
    if f7 >>> 1 == 0 && rd == rs1 && rd != 0 && sh != 0 then some (ci 0 2 rd sh) else none
  | 0x13, 5 =>
    -- srli (`imm[11:6]` = 0) and srai (`imm[11:6]` = 010000)
    let sh := (w >>> 20) % 64
    match reg' rd with
    | some rd' =>
      if rd == rs1 && sh != 0 then
        if f7 >>> 1 == 0 then some (cb 0 rd' sh)
        else if f7 >>> 1 == 0x10 then some (cb 1 rd' sh) else none
      else none
    | none => none
  | 0x37, _ =>
    -- lui
    let imm20 := w >>> 12
    if rd != 0 && rd != 2 && imm20 != 0 && (imm20 < 32 || 0xfffe0 ≤ imm20) then
      some (ci 3 1 rd (imm20 % 64))
    else none
  | 0x33, 0 =>
    if f7 == 0 then
      -- add
      if rd != 0 && rd == rs1 && rs2 != 0 then some (cr 9 2 rd rs2)
      else if rd != 0 && rd == rs2 && rs1 != 0 then some (cr 9 2 rd rs1)
      else none
    else if f7 == 0x20 then
      -- sub
      match reg' rd, reg' rs2 with
      | some rd', some rs2' => if rd == rs1 then some (ca 0x23 0 rd' rs2') else none
      | _, _ => none
    else none
  | 0x33, 4 | 0x33, 6 | 0x33, 7 =>
    -- xor, or, and
    let funct2 := if f3 == 4 then 1 else if f3 == 6 then 2 else 3
    if f7 != 0 then none
    else match reg' rd, reg' rs1, reg' rs2 with
      | some rd', _, some rs2' => if rd == rs1 then some (ca 0x23 funct2 rd' rs2') else
          if rd == rs2 then (reg' rs1).map (ca 0x23 funct2 rd' ·) else none
      | some rd', some rs1', none => if rd == rs2 then some (ca 0x23 funct2 rd' rs1') else none
      | _, _, _ => none
  | 0x3b, 0 =>
    match reg' rd, reg' rs1, reg' rs2 with
    | some rd', _, some rs2' =>
      if f7 == 0x20 then (if rd == rs1 then some (ca 0x27 0 rd' rs2') else none)
      else if f7 == 0 then
        -- addw, and its commuted form
        if rd == rs1 then some (ca 0x27 1 rd' rs2')
        else if rd == rs2 then (reg' rs1).map (ca 0x27 1 rd' ·) else none
      else none
    | some rd', some rs1', none =>
      if f7 == 0 && rd == rs2 then some (ca 0x27 1 rd' rs1') else none
    | _, _, _ => none
  | 0x03, 3 =>
    -- ld
    let off := immI
    (match reg' rd, reg' rs1 with
      | some rd', some rs1' =>
        if 0 ≤ off && off % 8 == 0 && off < 256 then some (C.clsD 3 rs1' rd' off.toNat) else none
      | _, _ => none)
    <|> (if rs1 == 2 && rd != 0 && 0 ≤ off && off % 8 == 0 && off < 512 then
        let u := off.toNat
        some (3 <<< 13 ||| bit u 5 12 ||| rd <<< 7 ||| ((u >>> 3) % 4) <<< 5 |||
          ((u >>> 6) % 8) <<< 2 ||| 2)
      else none)
  | 0x23, 3 =>
    -- sd
    let off := immS
    (match reg' rs1, reg' rs2 with
      | some rs1', some rs2' =>
        if 0 ≤ off && off % 8 == 0 && off < 256 then some (C.clsD 7 rs1' rs2' off.toNat) else none
      | _, _ => none)
    <|> (if rs1 == 2 && 0 ≤ off && off % 8 == 0 && off < 512 then
        let u := off.toNat
        some (7 <<< 13 ||| ((u >>> 3) % 8) <<< 10 ||| ((u >>> 6) % 8) <<< 7 ||| rs2 <<< 2 ||| 2)
      else none)
  | 0x23, 2 =>
    -- sw
    let off := immS
    (match reg' rs1, reg' rs2 with
      | some rs1', some rs2' =>
        if 0 ≤ off && off % 4 == 0 && off < 128 then some (C.csW rs1' rs2' off.toNat) else none
      | _, _ => none)
    <|> (if rs1 == 2 && 0 ≤ off && off % 4 == 0 && off < 256 then
        let u := off.toNat
        some (6 <<< 13 ||| ((u >>> 2) % 16) <<< 9 ||| ((u >>> 6) % 4) <<< 7 ||| rs2 <<< 2 ||| 2)
      else none)
  | 0x67, 0 =>
    -- jalr x0, 0(rs1)
    if rd == 0 && immI == 0 && rs1 != 0 then some (cr 8 2 rs1 0) else none
  | _, _ => none

/-- `w` as `n` hexadecimal digits, after `0x`. -/
def hexN (n w : Nat) : String :=
  let ds := Nat.toDigits 16 (w % 16 ^ n)
  "0x" ++ String.ofList (List.replicate (n - ds.length) '0' ++ ds)

/-- `w` as 8 hexadecimal digits, after `0x`. -/
def hex32 (w : Nat) : String := hexN 8 w

/-- The assembler directive emitting the instruction `w` (RISC-V Assembly
Programmer's Manual, ".insn": `.insn <length>, <value>` emits `value` as an
instruction of `length` bytes): its compressed encoding (`compress`) if it
has one, else its 32-bit encoding. -/
def insnLine (w : Nat) : String :=
  match compress w with
  | some h => s!".insn 2, {hexN 4 h}"
  | none => s!".insn 4, {hex32 w}"

end VG.RISCV64
