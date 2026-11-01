module

public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# Machine code of the 64-bit little-endian PowerPC model's instructions

**Trusted.** The 32-bit encoding of each straight-line instruction of the
model (`Instr`), of the comparison of a branch and of the return: what the
printer (`Print.lean`) emits, as `.long <word>` (a little-endian word, the
order in which a little-endian PowerPC fetches an instruction), in place of
the instruction's text, so that what runs is these words, not the
assembler's reading of a mnemonic. The branches (`beq`, `bne`, `b`), the
call (`bl`) and the address of a static (`adrSym`: `bcl`, `mflr` and the
`addis`/`addi` of its distance, whose bytes the linker writes) are still
printed as text for the assembler and linker to lay out.

The encodings are the Power ISA's (Version 3.0B), Book I: the instruction
formats of section 1.6 ("Instruction Formats": D, DS, X, XO, XFX, M, MD, VX,
VA and XX1), with each instruction's primary opcode and extended opcode
from its description, by the name in each definition's docs, and Appendix A
("Opcode Maps"). Where an extended mnemonic is printed (`li`, `lis`,
`subf`'s operand order, `mflr`, `mtlr`, `cmplwi`, `cmpldi`, `blr`) the
encoding is the instruction it stands for (Appendix C, "Assembler Extended
Mnemonics").

The fields' bit numbers in these docs are the Power ISA's: 0 is the most
significant bit of the word, 31 the least (`fld v i` puts `v` at the bits
counted from the least significant).

`encode` is `none` for an instruction whose operand does not fit its field,
which the printer reports as unencodable (`Printer.unencodable`) and the
emitter refuses (`Rust.checkEncodable`), rather than truncating it; and for
`adrSym`, which is text.
-/

@[expose] public section

namespace VG.PPC64LE

/-- The number `n` of `r<n>`. -/
def Reg.index : Reg → Nat
  | .r0 => 0 | .r2 => 2 | .r3 => 3 | .r4 => 4 | .r5 => 5 | .r6 => 6 | .r7 => 7 | .r8 => 8
  | .r9 => 9 | .r10 => 10 | .r11 => 11 | .r12 => 12 | .r14 => 14 | .r15 => 15 | .r16 => 16
  | .r17 => 17 | .r18 => 18 | .r19 => 19 | .r20 => 20 | .r21 => 21 | .r22 => 22 | .r23 => 23
  | .r24 => 24 | .r25 => 25 | .r26 => 26 | .r27 => 27 | .r28 => 28 | .r29 => 29 | .r30 => 30
  | .r31 => 31

namespace Enc

/-- The stack pointer, `r1`. -/
def sp : Nat := 1

/-- The value `v` as a field from bit `i` up, bits counted from the least
significant. -/
def fld (v i : Nat) : Nat := v <<< i

/-- X- and XO-form: primary opcode 31, `RT`/`RS` (bits 6–10), `RA` (11–15),
`RB` (16–20), extended opcode `xo` (21–30), `Rc = 0`. -/
def x (xo t a b : Nat) : Nat := fld 31 26 ||| fld t 21 ||| fld a 16 ||| fld b 11 ||| fld xo 1

/-- D-form: primary opcode `op` (0–5), `RT`/`RS` (6–10), `RA` (11–15), a
16-bit immediate (16–31). -/
def d (op t a imm16 : Nat) : Nat := fld op 26 ||| fld t 21 ||| fld a 16 ||| imm16

/-- A signed 16-bit immediate's bits, if `v` fits. -/
def si16 (v : Int) : Option Nat :=
  if -32768 ≤ v ∧ v < 32768 then some (v % 65536).toNat else none

/-- DS-form: primary opcode `op`, `RT`/`RS`, `RA`, a signed displacement
that is a multiple of 4 (`DS`, bits 16–29, its bits but the low two) and the
extended opcode `xo` (30–31). -/
def ds (op xo t a : Nat) (off : Int) : Option Nat :=
  if off % 4 = 0 then (si16 off).map fun v => d op t a (v ||| xo) else none

/-- MD-form (`rldicl`: `xo = 0`; `rldicr`: `xo = 1`): `RS`, `RA`, `sh[0:4]`
(bits 16–20), the 6-bit mask boundary stored as `mb[5] || mb[0:4]` (21–26),
`xo` (27–29), `sh[5]` (30). -/
def md (xo s a sh mb : Nat) : Nat :=
  fld 30 26 ||| fld s 21 ||| fld a 16 ||| fld (sh % 32) 11 ||| fld ((mb % 32) <<< 1 ||| mb >>> 5) 5 |||
    fld xo 2 ||| fld (sh >>> 5) 1

/-- VX-form: primary opcode 4, `VRT` (6–10), `VRA` (11–15), `VRB` (16–20),
extended opcode (21–31). -/
def vx (xo t a b : Nat) : Nat := fld 4 26 ||| fld t 21 ||| fld a 16 ||| fld b 11 ||| xo

/-- VA-form: primary opcode 4, `VRT`, `VRA`, `VRB`, `VRC` (21–25), extended
opcode (26–31). -/
def va (xo t a b c : Nat) : Nat := fld 4 26 ||| fld t 21 ||| fld a 16 ||| fld b 11 ||| fld c 6 ||| xo

/-- XX1-form: primary opcode 31, `T`/`S` (6–10), `RA`, `RB`, extended opcode
(21–30), `TX`/`SX` (31): the vector-scalar register is `32 * TX + T`, the
VMX register `vN` being VSR `32 + N` (`TX = 1`, `T = N`). -/
def xx1 (xo vsr a b : Nat) : Nat :=
  fld 31 26 ||| fld (vsr % 32) 21 ||| fld a 16 ||| fld b 11 ||| fld xo 1 ||| vsr / 32

end Enc

open Enc in
/-- The word of a vector instruction. -/
def VOp.encode : VOp → Option Nat
  -- "vcipher", "vcipherlast", "vncipher", "vncipherlast" (VX, 1288, 1289,
  -- 1352, 1353), "vsbox" (VX, 1480, `VRB = 0`).
  | .cipher inv last dr n m =>
    some (vx ((if inv then 1352 else 1288) + (if last then 1 else 0)) dr.ctorIdx n.ctorIdx m.ctorIdx)
  | .sbox dr n => some (vx 1480 dr.ctorIdx n.ctorIdx 0)
  -- "vshasigmaw", "vshasigmad" (VX, 1666, 1730): `ST` (bit 16), `SIX` (17–20).
  | .sha256 dr n st six =>
    if six < 16 then some (vx 1666 dr.ctorIdx n.ctorIdx ((if st then 16 else 0) ||| six)) else none
  | .sha512 dr n st six =>
    if six < 16 then some (vx 1730 dr.ctorIdx n.ctorIdx ((if st then 16 else 0) ||| six)) else none
  -- "vpmsumd" (VX, 1224).
  | .pmsumd dr n m => some (vx 1224 dr.ctorIdx n.ctorIdx m.ctorIdx)
  -- "vand", "vor", "vxor" (VX, 1028, 1156, 1220).
  | .logic op dr n m =>
    some (vx (match op with | .and => 1028 | .or => 1156 | .xor => 1220) dr.ctorIdx n.ctorIdx m.ctorIdx)
  -- "vsel" (VA, 42), "vperm" (VA, 43).
  | .sel dr n m mask => some (va 42 dr.ctorIdx n.ctorIdx m.ctorIdx mask.ctorIdx)
  | .perm dr n m c => some (va 43 dr.ctorIdx n.ctorIdx m.ctorIdx c.ctorIdx)
  -- "vadduwm", "vaddudm" (VX, 128, 192).
  | .add dw dr n m => some (vx (if dw then 192 else 128) dr.ctorIdx n.ctorIdx m.ctorIdx)
  -- "vsldoi" (VA, 44): `SHB` (bits 22–25, the `VRC` field's low four), `sh < 16`.
  | .sldoi dr n m sh => if sh < 16 then some (va 44 dr.ctorIdx n.ctorIdx m.ctorIdx sh) else none

open Enc in
/-- The words of an instruction, in order: one for each instruction
`Instr.asm` (`Print.lean`) names; `none` if an operand does not fit its
field, or for `adrSym`, which is text. -/
def Instr.encode : Instr → Option (List Nat)
  | .vop op => op.encode.map ([·])
  -- "lxvd2x" (XX1, 844), "stxvd2x" (XX1, 972), "mtvsrd" (XX1, 179, `RB =
  -- 0`), "mfvsrd" (XX1, 51, its GPR in the `RA` field).
  | .lxvd2x t a b | .lxvd2xTbl t a b .. => some [xx1 844 (t.ctorIdx + 32) a.index b.index]
  | .stxvd2x s a b => some [xx1 972 (s.ctorIdx + 32) a.index b.index]
  | .mtvsrd t a => some [xx1 179 (t.ctorIdx + 32) a.index 0]
  | .mfvsrd a s => some [xx1 51 (s.ctorIdx + 32) a.index 0]
  -- "add" (XO, 266), "subf" (XO, 40: `RT = RB - RA`, printed `subf d, m,
  -- n`), "mulld" (XO, 233), "mulhdu" (XO, 9), "addc" (XO, 10), "adde" (XO,
  -- 138), "addze" (XO, 202, `RB = 0`), "subfc" (XO, 8), "subfe" (XO, 136).
  | .add t a b => some [x 266 t.index a.index b.index]
  | .sub t n m => some [x 40 t.index m.index n.index]
  | .mul t a b => some [x 233 t.index a.index b.index]
  | .mulhu t a b => some [x 9 t.index a.index b.index]
  | .addc t a b => some [x 10 t.index a.index b.index]
  | .adde t a b => some [x 138 t.index a.index b.index]
  | .addze t a => some [x 202 t.index a.index 0]
  | .subc t n m => some [x 8 t.index m.index n.index]
  | .sube t n m => some [x 136 t.index m.index n.index]
  -- "addi" (D, 14), `subi` its negation, `li` with `RA = 0`; `lis` is
  -- "addis" (D, 15) with `RA = 0`.
  | .addi t a imm => (si16 imm).map fun v => [d 14 t.index a.index v]
  | .subi t a imm => (si16 (-(imm : Int))).map fun v => [d 14 t.index a.index v]
  | .li t imm => (si16 imm).map fun v => [d 14 t.index 0 v]
  | .lis t imm => some [d 15 t.index 0 imm.toNat]
  -- "ori" (D, 24), "oris" (D, 25): `RS` (6–10), `RA` (11–15), printed
  -- `ori ra, rs, ui`.
  | .ori a s imm => some [d 24 s.index a.index imm.toNat]
  | .oris a s imm => some [d 25 s.index a.index imm.toNat]
  -- "and" (X, 28), "or" (X, 444), "xor" (X, 316): `RS`, `RA`, `RB`, printed
  -- `and ra, rs, rb`.
  | .logic op a s b =>
    some [x (match op with | .and => 28 | .or => 444 | .xor => 316) s.index a.index b.index]
  -- "rlwinm" (M, 21): `RS`, `RA`, `SH` (16–20), `MB` (21–25), `ME` (26–30).
  | .rotr .w a s sh =>
    if sh < 32 then some [d 21 s.index a.index (fld ((32 - sh) % 32) 11 ||| fld 0 6 ||| fld 31 1)] else none
  | .lsr .w a s sh =>
    if sh < 32 then some [d 21 s.index a.index (fld ((32 - sh) % 32) 11 ||| fld sh 6 ||| fld 31 1)] else none
  -- "rldicl" (MD, 0), "rldicr" (MD, 1).
  | .rotr .d a s sh => if sh < 64 then some [md 0 s.index a.index ((64 - sh) % 64) 0] else none
  | .lsr .d a s sh => if sh < 64 then some [md 0 s.index a.index ((64 - sh) % 64) sh] else none
  | .lsl a s sh => if sh < 64 then some [md 1 s.index a.index sh (63 - sh)] else none
  -- "lwz" (D, 32), "stw" (D, 36), "lbz" (D, 34), "stb" (D, 38); "ld" (DS, 58,
  -- 0), "std" (DS, 62, 0).
  | .load .w t a off => (si16 off).map fun v => [d 32 t.index a.index v]
  | .store .w s a off => (si16 off).map fun v => [d 36 s.index a.index v]
  | .lbz t a off => (si16 off).map fun v => [d 34 t.index a.index v]
  | .stb s a off => (si16 off).map fun v => [d 38 s.index a.index v]
  | .load .d t a off => (ds 58 0 t.index a.index off).map ([·])
  | .store .d s a off => (ds 62 0 s.index a.index off).map ([·])
  -- "lwbrx" (X, 534), "ldbrx" (X, 532), "stwbrx" (X, 662), "stdbrx" (X, 660).
  | .loadRev .w t a b => some [x 534 t.index a.index b.index]
  | .loadRev .d t a b => some [x 532 t.index a.index b.index]
  | .storeRev .w s a b => some [x 662 s.index a.index b.index]
  | .storeRev .d s a b => some [x 660 s.index a.index b.index]
  -- "mfspr" (XFX, 339) and "mtspr" (XFX, 467) of the LR, SPR 8, whose field
  -- holds the number's halves swapped (`spr[5:9] || spr[0:4]`: 8 << 5).
  | .mflr t => some [x 339 t.index 8 0]
  | .mtlr s => some [x 467 s.index 8 0]
  -- The frames (`Isa.lean`'s `push`): "stdu" (DS, 62, 1) of `r1`, "std",
  -- "ld" and "addi" of `r1`.
  | .push r => do
    let a ← ds 62 1 sp sp (-48)
    let b ← ds 62 0 r.index sp 32
    return [a, b]
  | .pop r => do
    let a ← ds 58 0 r.index sp 32
    let b ← si16 48
    return [a, d 14 sp sp b]
  | .alloc bytes => (ds 62 1 sp sp (-(bytes : Int))).map ([·])
  | .free bytes => (si16 bytes).map fun v => [d 14 sp sp v]
  | .addSp t imm => (si16 imm).map fun v => [d 14 t.index sp v]
  | .adrSym .. => none

/-- The comparison of a branch's condition with zero: "cmpli" (D, 10) into
`cr0` (`BF = 0`), `L = 0` (`cmplwi`) or `L = 1` (`cmpldi`), `UI = 0`. -/
def Cond.cmpWord : Cond → Nat
  | .zero .w r | .nonzero .w r => Enc.d 10 0 r.index 0
  | .zero .d r | .nonzero .d r => Enc.d 10 1 r.index 0

/-- `blr`: "bclr" (XL, 19, 16) with `BO = 20` (branch always), `BI = 0`. -/
def retWord : Nat := 0x4E800020

/-- `w` as 8 hexadecimal digits, after `0x`. -/
def hex32 (w : Nat) : String :=
  let ds := Nat.toDigits 16 (w % 2 ^ 32)
  "0x" ++ String.ofList (List.replicate (8 - ds.length) '0' ++ ds)

/-- The assembler directive emitting the instruction `w`: `.long`, a 32-bit
word in the target's (little-endian) byte order. -/
def longLine (w : Nat) : String := s!".long {hex32 w}"

end VG.PPC64LE
