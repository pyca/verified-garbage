import VerifiedGarbage.Impl.Ed448.Arm.ScalarBase
import VerifiedGarbage.Impl.Ed448.Arm.Scalar

/-!
# Ed448 verification's equation on ARMv7

`vg_ed448_verify_equation(pk = r0, signature = r1, challenge = r2,
scratch = r3) -> r0`: 1 if the public key and `R` (the signature's first 57
bytes) decode, `S` (its last 57) is below `L`, and `[4][S]B = [4]R + [4][k]A`
for the 456-bit challenge `k`; 0 otherwise.

Field elements and their arithmetic are X448's on this target, as for
base-point multiplication (`ScalarBase.lean`): twenty-eight 16-bit limbs in
the 128-byte slots of the working space, with `r0` the working space and
`r6` the limb mask. The pointers to the public key and the signature stay in
`r8` and `r10`, which the field arithmetic preserves.

Everything is computed whatever the inputs, and the checks are accumulated
in `r12` (`BAD`), which stays 0 exactly when every one passes: each check
ORs into it a word that is 0 if and only if it passes. X448's full reduction
works on slot 1 alone, which is kept free for it: `Q`'s `Y` is in slot 21.

* The bits: byte `t` at `BITS` is bit `t` of `S` plus twice bit `t` of `k`.
* `S < L`: its byte 56 is 0 and its low 448 bits plus `2^448 - L` (the
  limbs `kLimb` of scalar reduction) do not carry out of 448 bits.
* Decoding a point (RFC 8032 §5.2.3) at `p` into the slots `xo` and `yo`:
  the twenty-eight limbs of `y`, which must be below `p` (they are equal to
  their full reduction) with bits 448–454 of the encoding 0; the sign bit to
  `SIGN`; `u = y² - 1`, `v = d y² - 1`, the candidate root
  `x = u³v (u⁵v³)^((p-3)/4)` (by `root`, X448's addition chain until
  `2^223 - 1`, then 223 squarings), the check `v x² = u`, the check that
  `x = 0` comes with the sign bit 0, and `x` swapped with `-x` by a mask if
  its low bit is not the sign bit.
* `A` is decoded into slots 6–7 (`Z = 1` in slot 10) and negated, and
  `Q = [S]B + [k](-A)` computed from the top bit down, as `[s]B` is: `Q`
  (slots 0, 21, 2) doubled, `B` (slots 8–10) added and swapped into `Q` by
  bit `t` of `S`, then `-A` added and swapped in by bit `t` of `k`.
* `R` is decoded into slots 8–9 (`B` is no longer needed), `Q` and `R` are
  doubled twice, and compared: `X_Q Z_R = X_R Z_Q` and `Y_Q Z_R = Y_R Z_Q`,
  fully reduced.

The result is 1 if `BAD` is 0. Every address and branch depends only on the
pointers.
-/

namespace VG.Impl.Ed448.Arm

open VG.Arm
open VG.Impl.X448.Arm (slot BITS TMP X2 saved ld st Op ops cswap freeze copy pass sqn)

/-! ## The working space -/

/-- The sign bit of the point being decoded. -/
def SIGN : Nat := 32

/-! ## Checks -/

/-- `BAD |= r3`. -/
def orBad : List Instr := [.dp .orr .r12 .r12 (.reg .r3)]

/-- `BAD |= 0` exactly when limb `i` of slot 1 is that of the slot at `a`. -/
def diffLimb (a i : Nat) : List Instr :=
  [ld .r3 (X2 + 4 * i), ld .r2 (a + 4 * i), .dp .eor .r3 .r3 (.reg .r2)] ++ orBad

/-- `BAD |= 0` exactly when slot 1 and the slot at `a` have the same limbs. -/
def diffSlot (a : Nat) : List Instr := (List.range 28).flatMap (diffLimb a)

/-- `BAD |= 0` exactly when the slots at `a` and `b` hold the same field
element: the one at `a` fully reduced (in slot 1) and copied back, the one at
`b` fully reduced in slot 1, and their limbs compared. -/
def eqSlots (a b : Nat) : List Instr :=
  copy X2 a ++ freeze ++ copy a X2 ++ copy X2 b ++ freeze ++ diffSlot a

/-- Limb `i` of the 56 bytes at `p + src` into `r3`. -/
def byteLimb (p : Reg) (src i : Nat) : List Instr :=
  [.ldrb .r3 p (src + 2 * i), .ldrb .r4 p (src + 2 * i + 1), .dp .add .r3 .r3 (.shifted .r4 .lsl 8)]

/-- The twenty-eight limbs of the 56 bytes at `p` into the slot at `o`. -/
def loadLimbs (p : Reg) (o : Nat) : List Instr :=
  (List.range 28).flatMap fun i => byteLimb p 0 i ++ [st .r3 (o + 4 * i)]

/-- Limb `i` of `S`'s low 448 bits plus that of `2^448 - L`, into `TMP`. -/
def sLimb (i : Nat) : List Instr :=
  byteLimb .r10 57 i ++
    [.movw .r2 (BitVec.ofNat 16 (kLimb i)), .dp .add .r3 .r3 (.reg .r2), st .r3 (TMP + 4 * i)]

/-- `BAD |= 0` exactly when `S` (the signature's last 57 bytes, at `r10 + 57`)
is below `L`: the carry out of 448 bits of its low limbs plus `2^448 - L`,
ORed with its byte 56. -/
def sCheck : List Instr :=
  (List.range 28).flatMap sLimb ++ pass TMP TMP ++
    [.ldrb .r3 .r10 113, .dp .orr .r3 .r3 (.reg .r5)] ++ orBad

/-! ## Decoding a point -/

/-- `z^((p-3)/4)` into slot 1 for `z` in slot 12, with the temporaries 14–20:
X448's addition chain (`invert`) as far as `z^(2^223 - 1)` (in slot 1) and
`z^(2^222 - 1)` (in slot 20), then `(z^(2^223 - 1))^(2^223) · z^(2^222 - 1)`. -/
def root : Prog isa :=
  .seq (ops [.copy (slot 14) (slot 12)]) <| .seq (sqn (slot 14) 1) <|
  .seq (ops [.mul (slot 14) (slot 14) (slot 12), .copy (slot 15) (slot 14)]) <|
  .seq (sqn (slot 15) 2) <| .seq (ops [.mul (slot 15) (slot 15) (slot 14), .copy (slot 16) (slot 15)]) <|
  .seq (sqn (slot 16) 4) <| .seq (ops [.mul (slot 16) (slot 16) (slot 15), .copy (slot 17) (slot 16)]) <|
  .seq (sqn (slot 17) 8) <| .seq (ops [.mul (slot 17) (slot 17) (slot 16), .copy (slot 18) (slot 17)]) <|
  .seq (sqn (slot 18) 16) <| .seq (ops [.mul (slot 18) (slot 18) (slot 17), .copy (slot 19) (slot 18)]) <|
  .seq (sqn (slot 19) 32) <| .seq (ops [.mul (slot 19) (slot 19) (slot 18), .copy (slot 20) (slot 19)]) <|
  .seq (sqn (slot 20) 64) <| .seq (ops [.mul (slot 20) (slot 20) (slot 19)]) <|
  .seq (sqn (slot 20) 64) <| .seq (ops [.mul (slot 20) (slot 20) (slot 19)]) <|
  .seq (sqn (slot 20) 16) <| .seq (ops [.mul (slot 20) (slot 20) (slot 17)]) <|
  .seq (sqn (slot 20) 8) <| .seq (ops [.mul (slot 20) (slot 20) (slot 16)]) <|
  .seq (sqn (slot 20) 4) <| .seq (ops [.mul (slot 20) (slot 20) (slot 15)]) <|
  .seq (sqn (slot 20) 2) <| .seq (ops [.mul (slot 20) (slot 20) (slot 14), .copy X2 (slot 20)]) <|
  .seq (sqn X2 1) <| .seq (ops [.mul X2 X2 (slot 12)]) <|
  .seq (sqn X2 223) (ops [.mul X2 X2 (slot 20)])

/-- The 57 bytes at `p`: `y`'s limbs into slot `yo`, the sign bit to `SIGN`,
and `BAD |= 0` exactly when bits 448–454 are 0 and `y < p`. -/
def decodeY (p : Reg) (yo : Nat) : List Instr :=
  loadLimbs p (slot yo) ++
    [.ldrb .r3 p 56, .mov .r2 (.shifted .r3 .lsr 7), st .r2 SIGN, .dp .and .r3 .r3 (.imm 0x7f)] ++
    orBad ++ copy X2 (slot yo) ++ freeze ++ diffSlot (slot yo)

/-- From `y` in slot `yo` (with 1 in slot 10 and `d` in slot 11): `v` in
slot 3, `u` in slot 13, `u³v` in slot `xo`, and `u⁵v³` in slot 12. -/
def decodeUV (yo xo : Nat) : List Op :=
  [.mul (slot 12) (slot yo) (slot yo), .sub (slot 13) (slot 12) (slot 10),
    .mul (slot 3) (slot 11) (slot 12), .sub (slot 3) (slot 3) (slot 10),
    .mul (slot 4) (slot 13) (slot 3), .mul (slot 4) (slot 4) (slot 4),
    .mul (slot 5) (slot 13) (slot 13), .mul (slot 5) (slot 5) (slot 13),
    .mul (slot xo) (slot 5) (slot 3), .mul (slot 12) (slot xo) (slot 4)]

/-- `x` in slot `xo`, from `u³v` there and the root in slot 1, and `v x²` in
slot 12. -/
def decodeX (xo : Nat) : List Op :=
  [.mul (slot xo) (slot xo) X2, .mul (slot 12) (slot xo) (slot xo), .mul (slot 12) (slot 3) (slot 12)]

/-- `-x = (x - x) - x` in slot 12. -/
def negX (xo : Nat) : List Op := [.sub (slot 12) (slot xo) (slot xo), .sub (slot 12) (slot 12) (slot xo)]

/-- `r2 = ⋁` the limbs of slot 1. -/
def orLimbs : List Instr :=
  ld .r2 X2 :: (List.range 27).flatMap fun i => [ld .r3 (X2 + 4 * (i + 1)), .dp .orr .r2 .r2 (.reg .r3)]

/-- The sign, with `-x` in slot 12: `x` fully reduced in slot 1; `BAD |= 0`
exactly when `x ≠ 0` or the sign bit is 0; then `x` swapped with `-x` by the
mask of `x`'s low bit differing from the sign bit. -/
def decodeSign (xo : Nat) : List Instr :=
  copy X2 (slot xo) ++ freeze ++ orLimbs ++
    [.dp .sub .r2 .r2 (.imm 1), .mov .r2 (.shifted .r2 .lsr 31), ld .r3 SIGN,
      .dp .and .r2 .r2 (.reg .r3), .dp .orr .r12 .r12 (.reg .r2),
      ld .r2 X2, .dp .and .r2 .r2 (.imm 1), .dp .eor .r2 .r2 (.reg .r3), .mov .r5 (.imm 0),
      .dp .sub .r5 .r5 (.reg .r2)] ++ cswap (slot xo) (slot 12)

/-- Decode the 57 bytes at `p` into slots `xo` and `yo`. -/
def decode (p : Reg) (xo yo : Nat) : Prog isa :=
  .seq (.block (decodeY p yo)) <| .seq (ops (decodeUV yo xo)) <| .seq root <|
  .seq (ops (decodeX xo)) <| .seq (.block (eqSlots (slot 12) (slot 13))) <|
  .seq (ops (negX xo)) (.block (decodeSign xo))

/-! ## `[S]B + [k](-A)` -/

/-- `R = 2R` in slots `x`, `y`, `z` (RFC 8032 §5.2.4's doubling, as in
`doubleOps`), with the temporaries 12–19. -/
def doubleAt (x y z : Nat) : List Op := [
  .add (slot 12) (slot x) (slot y), .mul (slot 12) (slot 12) (slot 12), .mul (slot 13) (slot x) (slot x),
  .mul (slot 14) (slot y) (slot y), .add (slot 15) (slot 13) (slot 14), .mul (slot 16) (slot z) (slot z),
  .add (slot 17) (slot 16) (slot 16), .sub (slot 17) (slot 15) (slot 17), .sub (slot 18) (slot 12) (slot 15),
  .mul (slot x) (slot 18) (slot 17), .sub (slot 19) (slot 13) (slot 14), .mul (slot y) (slot 15) (slot 19),
  .mul (slot z) (slot 15) (slot 17)]

/-- `T = Q + (x : y : 1)` into slots 3–5 for `Q` in slots 0, 21, 2 (the
addition of `addOps`, with the second point in slots `x`, `y` and 10), with
the temporaries 12–20. -/
def addAt (x y : Nat) : List Op := [
  .mul (slot 12) (slot 2) (slot 10), .mul (slot 13) (slot 12) (slot 12), .mul (slot 14) (slot 0) (slot x),
  .mul (slot 15) (slot 21) (slot y), .mul (slot 16) (slot 11) (slot 14), .mul (slot 16) (slot 16) (slot 15),
  .sub (slot 17) (slot 13) (slot 16), .add (slot 18) (slot 13) (slot 16), .add (slot 19) (slot 0) (slot 21),
  .add (slot 20) (slot x) (slot y), .mul (slot 19) (slot 19) (slot 20), .mul (slot 20) (slot 12) (slot 17),
  .sub (slot 19) (slot 19) (slot 14), .sub (slot 19) (slot 19) (slot 15), .mul (slot 3) (slot 20) (slot 19),
  .mul (slot 20) (slot 12) (slot 18), .sub (slot 19) (slot 15) (slot 14), .mul (slot 4) (slot 20) (slot 19),
  .mul (slot 5) (slot 17) (slot 18)]

/-- `r5 = -bit`, for bit `r11` of `S` (`hi = false`) or of `k` (`hi = true`). -/
def vmask (hi : Bool) : List Instr :=
  [.dp .add .r7 .r0 (.reg .r11), .ldrb .r3 .r7 BITS,
    if hi then .mov .r3 (.shifted .r3 .lsr 1) else .dp .and .r3 .r3 (.imm 1),
    .mov .r5 (.imm 0), .dp .sub .r5 .r5 (.reg .r3)]

/-- `T` swapped into `Q` by the mask `r5`. -/
def vswap : List Instr := cswap (slot 0) (slot 3) ++ cswap (slot 21) (slot 4) ++ cswap (slot 2) (slot 5)

/-- One bit `t = r11 - 1`, from the top. -/
def vstep : Prog isa :=
  .seq (.block [.dp .sub .r11 .r11 (.imm 1)]) <| .seq (ops (doubleAt 0 21 2)) <|
  .seq (ops (addAt 8 9)) <| .seq (.block (vmask false ++ vswap)) <|
  .seq (ops (addAt 6 7)) (.block (vmask true ++ vswap ++ [.cmp .r11 (.imm 0)]))

/-- The 456 bits, from 455 down to 0. -/
def vloop : Prog isa := .seq (.block [.movw .r11 456]) (.loop vstep .ne)

/-! ## The function -/

/-- Bit `j` of the bytes of `S` (in `r3`) and `k` (in `r9`) to `BITS + j`
from `r7`, as bit 0 and bit 1. -/
def vbitJ (j : Nat) : List Instr :=
  [.mov .r1 (if j = 0 then .reg .r3 else .shifted .r3 .lsr j), .dp .and .r1 .r1 (.imm 1),
    .mov .r4 (if j = 0 then .reg .r9 else .shifted .r9 .lsr j), .dp .and .r4 .r4 (.imm 1),
    .dp .add .r1 .r1 (.shifted .r4 .lsl 1), .strb .r1 .r7 (BITS + j)]

/-- Byte `r11` of `S` (at `r10 + 57`) and of `k` (at `r2`) expanded to bytes
`BITS + 8 r11 + j`. -/
def vbitsBody : List Instr :=
  [.dp .add .r7 .r10 (.reg .r11), .ldrb .r3 .r7 57, .dp .add .r7 .r2 (.reg .r11), .ldrb .r9 .r7 0,
    .dp .add .r7 .r0 (.shifted .r11 .lsl 3)] ++
    (List.range 8).flatMap vbitJ ++ [.dp .add .r11 .r11 (.imm 1), .cmp .r11 (.imm 57)]

/-- All 456 bits of `S` and `k`. -/
def vbits : Prog isa := .seq (.block [.mov .r11 (.imm 0)]) (.loop (.block vbitsBody) .ne)

/-- The callee-saved registers saved at the working space (`r3`), the
pointers to `A` and the signature into `r8` and `r10`, the working space into
`r0` and the limb mask into `r6`. -/
def ventry : List Instr :=
  (List.range 8).map (fun i => .str (saved[i]!) .r3 (4 * i)) ++
    [.mov .r12 (.reg .r0), .mov .r0 (.reg .r3), .movw .r6 65535, .mov .r8 (.reg .r12),
      .mov .r10 (.reg .r1)]

/-- `BAD = 0`, the check of `S`, and the slots initialized as for base-point
multiplication, with `Q`'s `Y` (1) in slot 21. -/
def vstart : List Instr := [.mov .r12 (.imm 0)] ++ sCheck ++ initSlots ++ copy (slot 21) X2

/-- `[4]Q` and `[4]R` compared (`BAD |= 0` exactly when they are the same
point), the callee-saved registers restored, and `r0 = (BAD == 0)`. -/
def vfinish : Prog isa :=
  .seq (ops (doubleAt 0 21 2)) <| .seq (ops (doubleAt 0 21 2)) <|
  .seq (ops (doubleAt 8 9 10)) <| .seq (ops (doubleAt 8 9 10)) <|
  .seq (ops [.mul (slot 12) (slot 0) (slot 10), .mul (slot 13) (slot 8) (slot 2)]) <|
  .seq (.block (eqSlots (slot 12) (slot 13))) <|
  .seq (ops [.mul (slot 12) (slot 21) (slot 10), .mul (slot 13) (slot 9) (slot 2)]) <|
  .block (eqSlots (slot 12) (slot 13) ++
    [.dp .sub .r1 .r12 (.imm 1), .mov .r1 (.shifted .r1 .lsr 31)] ++
    (List.range 8).map (fun i => ld (saved[i]!) (4 * i)) ++ [.mov .r0 (.reg .r1)])

/-- `vg_ed448_verify_equation(pk = r0, signature = r1, challenge = r2, scratch = r3) -> r0`. -/
def verifyEquation : Prog isa :=
  .seq (.block ventry) <| .seq vbits <| .seq (.block vstart) <| .seq (decode .r8 6 7) <|
  .seq (ops [.sub (slot 6) (slot 0) (slot 6)]) <| .seq vloop <| .seq (decode .r10 8 9) vfinish

end VG.Impl.Ed448.Arm
