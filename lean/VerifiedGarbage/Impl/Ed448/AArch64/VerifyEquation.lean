import VerifiedGarbage.Impl.Ed448.AArch64.Point56

/-!
# Ed448 verification's equation on AArch64: the checks, the decodings and the entry

The parts of `vg_ed448_verify_equation` (`VerifyWindow.lean`) with X448's
memory-resident field arithmetic (`Impl/X448/AArch64/Weak.lean`, eight 56-bit
limbs per slot). The checks are accumulated in `x20`, which stays 0 exactly
when every one passes: each check ORs into it a word that is 0 if and only if
it passes.

* `S < L` (`sCheck`): its byte 56 is 0, and its low 448 bits plus `2^448 - L`
  do not carry (`carryK`: eight 56-bit chunks of seven bytes, added with
  carries).
* Decoding a point (RFC 8032 §5.2.3) at `x0` or `x1` into the slots `xo` and
  `yo` (`decode`): the eight seven-byte chunks of `y` into slot `yo`; `y < p`
  (`y + 2^224 + 1` does not carry) and bits 448–454 of the encoding 0; the sign
  bit kept in `x17`; `u = y² - 1`, `v = d y² - 1`, the candidate root `x = u³v
  (u⁵v³)^((p-3)/4)` (a call of `vg_gf448_r56_pow_p34`, `Point56.lean`, which runs `root`:
  X448's addition chain until `2^223 - 1`, then 223 squarings), the check `v x² = u`, the check that `x = 0` comes with the
  sign bit 0, and `x` swapped with `-x` by a mask (kept in `x17` while `-x`
  is computed) if its low bit is not the sign bit. A comparison or a low bit
  uses `x`, or the elements compared, fully reduced into `X2` (slot 1) as
  sixteen 28-bit limbs (`canon`, with X448's `toLegacy` and `freeze`).
* The bits of a scalar, one per byte (`bitsAt`), and the entry (`ventry`).
-/

namespace VG.Impl.Ed448.AArch64

open VG.AArch64
open VG.Impl.X448.AArch64 (ld st slot BITS X2 T0 T1 T2 T3 T4 T5 T6 T7)

/-! ## The working space -/

/-- A fully reduced field element (sixteen 28-bit limbs), to compare another with. -/
def CAN : Nat := 4864
/-! ## Checks -/

/-- `x20 |= x5`. -/
def orBad : List Instr := [.logic .orr .x .x20 .x20 .x5]

/-- `x5 = 1` if `x5 = 0`, else `0`: the no-borrow flag of `0 - x5`. -/
def isZero : List Instr := [.movz .x .x6 0 0, .subs .x .x7 .x6 .x5, .adc .x .x5 .x6 .x6]

/-- Slot `a` fully reduced into `X2`, as sixteen 28-bit limbs. -/
def canon (a : Nat) : List Instr :=
  Curve448.AArch64.copy X2 (slot a) ++ Curve448.AArch64.toLegacy X2 ++ Impl.X448.AArch64.freeze

/-- `x5` = the OR of the sixteen words of `X2` XORed with those of `CAN`. -/
def diffCan : List Instr :=
  [.movz .x .x5 0 0] ++ (List.range 16).flatMap fun i =>
    [ld .x4 (X2 + 8 * i), ld .x6 (CAN + 8 * i), .logic .eor .x .x4 .x4 .x6, .logic .orr .x .x5 .x5 .x4]

/-- `x20 |= 0` exactly when slots `a` and `b` hold the same field element. -/
def eqSlots (a b : Nat) : List Instr :=
  canon a ++ Impl.X448.AArch64.copy CAN X2 ++ canon b ++ diffCan ++ orBad

/-- `x4` = the seven bytes at `rp + o`, little-endian, from the highest. -/
def bytes7 (rp : Reg) (o : Nat) : List Instr :=
  [.movz .x .x4 0 0] ++ (List.range 7).flatMap fun j =>
    [.lsl .x .x4 .x4 8, .ldrb .x7 rp (o + (6 - j)), .add .x .x4 .x4 .x7]

/-- `x5` = the carry out of the 56 bytes at `rp + o` plus `K`, as eight
56-bit chunks with carries. -/
def carryK (rp : Reg) (o K : Nat) : List Instr :=
  [.movz .x .x5 0 0] ++ (List.range 8).flatMap fun i =>
    bytes7 rp (o + 7 * i) ++
      Impl.X448.AArch64.Base.const64 .x6 (BitVec.ofNat 64 ((K >>> (56 * i)) % 2 ^ 56)) ++
      [.add .x .x4 .x4 .x6, .add .x .x4 .x4 .x5, .lsr .x .x5 .x4 56]

/-- `x20 |= 0` exactly when the 57 bytes at `x1 + 57` are below `L`. -/
def sCheck : List Instr :=
  carryK .x1 57 (2 ^ 448 - Spec.Ed448.L) ++ orBad ++ [.ldrb .x5 .x1 113] ++ orBad

/-! ## Decoding a point -/

/-- `decodeUV yo xo` (`Formulas.lean`) with the register-resident operations, whose
difference may not write an operand: `d y²` goes through slot 4. `u = y² - 1` in 13, `v = d y² - 1`
in 3, `(uv)²` in 4, `u³` in 5, `u³v` in `xo` and `u⁵v³` in 12. -/
def decodeUVOps (yo xo : Nat) : List X448.AArch64.Fast.Op :=
  [.mul (slot 12) (slot yo) (slot yo), .sub (slot 13) (slot 12) (slot 10), .mul (slot 4) (slot 11) (slot 12),
   .sub (slot 3) (slot 4) (slot 10), .mul (slot 4) (slot 13) (slot 3), .mul (slot 4) (slot 4) (slot 4),
   .mul (slot 5) (slot 13) (slot 13), .mul (slot 5) (slot 5) (slot 13), .mul (slot xo) (slot 5) (slot 3),
   .mul (slot 12) (slot xo) (slot 4)]

/-- `x = u³v · root` into `xo`, and `x² v` into 12. -/
def decodeXOps (xo : Nat) : List X448.AArch64.Fast.Op :=
  [.mul (slot xo) (slot xo) (slot 21), .mul (slot 12) (slot xo) (slot xo), .mul (slot 12) (slot 12) (slot 3)]

/-- The 57 bytes at `rp`: `y`'s eight seven-byte chunks into slot `yo`, the
sign bit into `x17`, and `x20 |= 0` exactly when `y < p` and bits 448–454
are 0. -/
def decodeY (rp : Reg) (yo : Nat) : List Instr :=
  (List.range 8).flatMap (fun i => bytes7 rp (7 * i) ++ [st .x4 (slot yo + 8 * i)]) ++
  carryK rp 0 (2 ^ 224 + 1) ++ orBad ++
  [.ldrb .x5 rp 56, .lsr .x .x17 .x5 7, .movz .x .x6 0x7f 0, .logic .and .x .x5 .x5 .x6] ++ orBad

/-- `x` fully reduced into `X2`; `x20 |= 0` exactly when `x ≠ 0` or the sign
bit is 0. -/
def zeroSign (xo : Nat) : List Instr :=
  canon xo ++ [.movz .x .x5 0 0] ++
  (List.range 16).flatMap (fun i => [ld .x4 (X2 + 8 * i), .logic .orr .x .x5 .x5 .x4]) ++ isZero ++
  [.logic .and .x .x5 .x5 .x17] ++ orBad

/-- `x17` = the mask of `x`'s low bit (from `X2`) differing from the sign bit
(in `x17`). -/
def negMask : List Instr :=
  [ld .x4 X2, .movz .x .x6 1 0, .logic .and .x .x4 .x4 .x6, .logic .eor .x .x4 .x4 .x17,
    .movz .x .x6 0 0, .sub .x .x17 .x6 .x4]

/-- `x` swapped with `-x` (in slot 12) by the mask in `x17`. -/
def negSwap (xo : Nat) : List Instr :=
  [.addImm .x .x6 .x17 0] ++ Curve448.AArch64.cswap (slot xo) (slot 12)

/-- Where decoding keeps the sign bit across the field operations, which use `x17`. -/
def SIGN : Nat := 16

/-- Decode the 57 bytes at `rp` into slots `xo` and `yo`, with the register-resident
arithmetic: 1 is written into slot 10 (the differences need their operands below the products'
bound), the sign bit is kept at `SIGN`, and `-x` is `0 - x`, from zero written into slot 13 (`u`,
once compared). -/
def decode (rp : Reg) (xo yo : Nat) : Prog isa :=
  .seq (.block (decodeY rp yo ++ [st .x17 SIGN] ++ Impl.X448.AArch64.Base.constSlot (slot 10) 1)) <|
  .seq (X448.AArch64.Fast.ops (decodeUVOps yo xo)) <| .seq Point56.powCall <|
  .seq (X448.AArch64.Fast.ops (decodeXOps xo)) <|
  .seq (.block (eqSlots 12 13 ++ Impl.X448.AArch64.Base.constSlot (slot 13) 0)) <|
  .seq (X448.AArch64.Fast.ops [.sub (slot 12) (slot 13) (slot xo)]) <|
  .block ([ld .x17 SIGN] ++ zeroSign xo ++ negMask ++ negSwap xo)

/-! ## A scalar's bits -/

/-- Bit `j` of scalar byte `x19` (at `src + so + x19`) at `x3 + 8 x19 + d1 + d2 + j`. -/
def bitsBodyAt (src : Reg) (so d1 d2 : Nat) : List Instr :=
  [.add .x .x11 src .x19, .ldrb .x4 .x11 so, .lsl .x .x11 .x19 3, .add .x .x11 .x3 .x11,
    .addImm .x .x11 .x11 d1] ++
  (List.range 8).flatMap (fun j =>
    [.lsr .x .x5 .x4 j, .logic .and .x .x5 .x5 .x8, .strb .x5 .x11 (d2 + j)]) ++
  [.addImm .x .x19 .x19 1, .subImm .x .x11 .x19 57]

/-- The 456 bits of the 57 bytes at `src + so`. -/
def bitsAt (src : Reg) (so d1 d2 : Nat) : Prog isa :=
  .seq (.block [.movz .x .x19 0 0, .movz .x .x8 1 0]) (.loop (.block (bitsBodyAt src so d1 d2)) (.nonzero .x .x11))

/-! ## The entry -/

/-- Where the return address is kept, since the function calls others: after the challenge's
copy. -/
def LRS : Nat := 3008

/-- `x12 = 2^28 - 1`, `x19`, `x20` and the return address saved, `x20 = 0`, and every slot
zeroed; then `B` and the constants 1 and `d`. -/
def ventry : List Instr :=
  [.movz .x .x12 0xffff 0, .movk .x .x12 0x0fff 1, st .x19 0, st .x20 8, st .x30 LRS, .movz .x .x20 0 0,
    .movz .x .x4 0 0] ++
  (List.range 352).map (fun i => st .x4 (slot 0 + 8 * i)) ++
  Impl.X448.AArch64.Base.constSlot (slot 8) Spec.Ed448.basePoint.X ++
  Impl.X448.AArch64.Base.constSlot (slot 9) Spec.Ed448.basePoint.Y ++
  Impl.X448.AArch64.Base.constSlot (slot 10) 1 ++ Impl.X448.AArch64.Base.constSlot (slot 11) Spec.Ed448.d

/-- `A` decoded into slots 6–7 and negated: `x` (below the products' bound, a product by 1 in
slot 10) subtracted from zero in slot 13. -/
def vdecodeA : Prog isa :=
  .seq (decode .x0 6 7) <| .seq (X448.AArch64.Fast.ops [.mul (slot 6) (slot 6) (slot 10)]) <|
  .seq (.block (Impl.X448.AArch64.Base.constSlot (slot 13) 0)) <|
  X448.AArch64.Fast.ops [.sub (slot 12) (slot 13) (slot 6), .copy (slot 6) (slot 12)]

end VG.Impl.Ed448.AArch64
