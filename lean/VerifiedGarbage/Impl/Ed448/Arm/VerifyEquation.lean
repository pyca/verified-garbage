module

public import VerifiedGarbage.Impl.Ed448.Arm.ScalarBase
public import VerifiedGarbage.Impl.Ed448.Arm.Scalar

/-!
# Ed448 verification's equation on ARMv7

`vg_ed448_verify_equation(pk = r0, signature = r1, challenge = r2,
scratch = r3) -> r0`: 1 if the public key and `R` (the signature's first 57
bytes) decode, `S` (its last 57) is below `L`, and `[4][S]B = [4]R + [4][k]A`
for the 456-bit challenge `k`; 0 otherwise.

Field elements and their arithmetic are X448's on this target, as for
base-point multiplication (`ScalarBase.lean`): twenty-eight 16-bit limbs in
the 128-byte slots of the working space, with `r0` the working space and
`r6` the limb mask; multiplications, additions and subtractions are calls of
the `vg_gf448_r16_*` functions, which change `r1`–`r3`, `r12` and `lr` (and
so the link register is kept at `LR`) but keep `r8`, `r10` and `r11`. The
pointer to the public key stays in `r8` until the decoding loop; the one to the
signature is in `r12`, which `decode` reads only before its first call.

Everything is computed whatever the inputs, and the checks are accumulated
in `r10` (`BAD`), which stays 0 exactly when every one passes: each check
ORs into it a word that is 0 if and only if it passes. X448's full reduction
works on slot 1 alone, which is kept free for it: `Q`'s `Y` is in slot 21
(between the decodings and the comparison, where nothing is reduced, slot 1
holds the `Z` of a multiple of `-A`).

* The bits: byte `t` at `VBITS` is bit `t` of `S` plus twice bit `t` of `k`
  (`vbits`), and then, once `A` is decoded, plus twice digit `t` of `k`
  (`vrecode`): `k`'s digits, each zero or odd and below 16, sum to `k` at the
  powers of two.
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
* `R` and then `A` are decoded into slots 6–7 (`vdecode`), `R` kept at `RX`
  and `RY` (`Z = 1` in slot 10). `A` is negated, its odd multiples
  `[1](-A), [3](-A), …, [15](-A)` are put in a table at `VTAB` (`vtable`), and
  `Q = [S]B + [k](-A)` computed from the top bit down: `Q` (slots 0, 21, 2)
  doubled for each of the 456 bits; in the last 114, the rows of
  base-point multiplication's comb (`ScalarBase.lean`), the table's entry of
  the row's four bits of `S` selected into slots 8–9 and added, so that the
  comb shares the doublings; and, where digit `t` of `k` is not zero, the
  entry of `-A`'s table for that digit loaded into slots 6, 7 and 1 and
  added: a sliding window of four bits on `k`, in the same doublings. The
  signature and the challenge are public (a verification may leak its
  inputs), so the window's entry is only added where the digit is not zero,
  and loaded from the digit's address: the byte of the bit of `S` and the
  digit is loaded into `r8`, which the field functions never write, and the
  branch and the address are on it.
* `R` is copied into slots 8–9 (`B` is no longer needed), `Q` and `R` are
  doubled twice (a loop, `vdouble`), and compared: `X_Q Z_R = X_R Z_Q` and `Y_Q Z_R = Y_R Z_Q`,
  fully reduced.

The result is 1 if `BAD` is 0. Every address depends only on the pointers
and on `k`'s digits, and every branch on the pointers and on the bits of `S`
and `k`.
-/

@[expose] public section

namespace VG.Impl.Ed448.Arm

open VG.Arm
open VG.Impl.X448.Arm (slot TMP X2 saved ld st Op ops cswap freeze copy pass sqn)

/-! ## The working space -/

/-- The sign bit of the point being decoded. -/
def SIGN : Nat := 32

/-- `R`, decoded first, kept while `A` is decoded and `Q` computed: its `X` and `Y`, where no
field operation writes (between the slots and `VBITS`). -/
def RX : Nat := 2880
def RY : Nat := 2992

/-- The bits of `S` and `k`, one byte per bit. -/
def VBITS : Nat := 3104

/-- The link register, which the calls change. -/
def LR : Nat := 3560

/-! ## Checks -/

/-- `BAD |= r3`. -/
def orBad : List Instr := [.dp .orr .r10 .r10 (.reg .r3)]

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
  byteLimb .r12 57 i ++
    [.movw .r2 (BitVec.ofNat 16 (kLimb i)), .dp .add .r3 .r3 (.reg .r2), st .r3 (TMP + 4 * i)]

/-- `BAD |= 0` exactly when `S` (the signature's last 57 bytes, at `r12 + 57`)
is below `L`: the carry out of 448 bits of its low limbs plus `2^448 - L`,
ORed with its byte 56. -/
def sCheck : List Instr :=
  (List.range 28).flatMap sLimb ++ pass TMP TMP ++
    [.ldrb .r3 .r12 113, .dp .orr .r3 .r3 (.reg .r5)] ++ orBad

/-! ## Decoding a point -/

/-- `z^((p-3)/4)` into slot 1 for `z` in slot 12, with the temporaries 14–20:
X448's addition chain (`invert`) as far as `z^(2^223 - 1)` (in slot 1) and
`z^(2^222 - 1)` (in slot 20), then `(z^(2^223 - 1))^(2^223) · z^(2^222 - 1)`. -/
def root (u : Bool) : Prog isa :=
  .seq (ops u [.copy (slot 14) (slot 12)]) <| .seq (sqn u (slot 14) 1) <|
  .seq (ops u [.mul (slot 14) (slot 14) (slot 12), .copy (slot 15) (slot 14)]) <|
  .seq (sqn u (slot 15) 2) <| .seq (ops u [.mul (slot 15) (slot 15) (slot 14), .copy (slot 16) (slot 15)]) <|
  .seq (sqn u (slot 16) 4) <| .seq (ops u [.mul (slot 16) (slot 16) (slot 15), .copy (slot 17) (slot 16)]) <|
  .seq (sqn u (slot 17) 8) <| .seq (ops u [.mul (slot 17) (slot 17) (slot 16), .copy (slot 18) (slot 17)]) <|
  .seq (sqn u (slot 18) 16) <| .seq (ops u [.mul (slot 18) (slot 18) (slot 17), .copy (slot 19) (slot 18)]) <|
  .seq (sqn u (slot 19) 32) <| .seq (ops u [.mul (slot 19) (slot 19) (slot 18), .copy (slot 20) (slot 19)]) <|
  .seq (sqn u (slot 20) 64) <| .seq (ops u [.mul (slot 20) (slot 20) (slot 19)]) <|
  .seq (sqn u (slot 20) 64) <| .seq (ops u [.mul (slot 20) (slot 20) (slot 19)]) <|
  .seq (sqn u (slot 20) 16) <| .seq (ops u [.mul (slot 20) (slot 20) (slot 17)]) <|
  .seq (sqn u (slot 20) 8) <| .seq (ops u [.mul (slot 20) (slot 20) (slot 16)]) <|
  .seq (sqn u (slot 20) 4) <| .seq (ops u [.mul (slot 20) (slot 20) (slot 15)]) <|
  .seq (sqn u (slot 20) 2) <| .seq (ops u [.mul (slot 20) (slot 20) (slot 14), .copy X2 (slot 20)]) <|
  .seq (sqn u X2 1) <| .seq (ops u [.mul X2 X2 (slot 12)]) <|
  .seq (sqn u X2 223) (ops u [.mul X2 X2 (slot 20)])

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
      .dp .and .r2 .r2 (.reg .r3), .dp .orr .r10 .r10 (.reg .r2),
      ld .r2 X2, .dp .and .r2 .r2 (.imm 1), .dp .eor .r2 .r2 (.reg .r3), .mov .r5 (.imm 0),
      .dp .sub .r5 .r5 (.reg .r2)] ++ cswap (slot xo) (slot 12)

/-- Decode the 57 bytes at `p` into slots `xo` and `yo`. -/
def decode (u : Bool) (p : Reg) (xo yo : Nat) : Prog isa :=
  .seq (.block (decodeY p yo)) <| .seq (ops u (decodeUV yo xo)) <| .seq (root u) <|
  .seq (ops u (decodeX xo)) <| .seq (.block (eqSlots (slot 12) (slot 13))) <|
  .seq (ops u (negX xo)) (.block (decodeSign xo))

/-! ## `[S]B + [k](-A)` -/

/-- `R = 2R` in slots `x`, `y`, `z` (RFC 8032 §5.2.4's doubling, as in
`doubleOps`), with the temporaries 12–19. -/
def doubleAt (x y z : Nat) : List Op := [
  .add (slot 12) (slot x) (slot y), .mul (slot 12) (slot 12) (slot 12), .mul (slot 13) (slot x) (slot x),
  .mul (slot 14) (slot y) (slot y), .add (slot 15) (slot 13) (slot 14), .mul (slot 16) (slot z) (slot z),
  .add (slot 17) (slot 16) (slot 16), .sub (slot 17) (slot 15) (slot 17), .sub (slot 18) (slot 12) (slot 15),
  .mul (slot x) (slot 18) (slot 17), .sub (slot 19) (slot 13) (slot 14), .mul (slot y) (slot 15) (slot 19),
  .mul (slot z) (slot 15) (slot 17)]

/-- `T = Q + (x : y : z)` into slots 3–5 for `Q` in slots 0, 21, 2 (the
addition of `addOps`, with the second point in slots `x`, `y` and `z`), with
the temporaries 12–20. -/
def addAt (x y z : Nat) : List Op := [
  .mul (slot 12) (slot 2) (slot z), .mul (slot 13) (slot 12) (slot 12), .mul (slot 14) (slot 0) (slot x),
  .mul (slot 15) (slot 21) (slot y), .mul (slot 16) (slot 11) (slot 14), .mul (slot 16) (slot 16) (slot 15),
  .sub (slot 17) (slot 13) (slot 16), .add (slot 18) (slot 13) (slot 16), .add (slot 19) (slot 0) (slot 21),
  .add (slot 20) (slot x) (slot y), .mul (slot 19) (slot 19) (slot 20), .mul (slot 20) (slot 12) (slot 17),
  .sub (slot 19) (slot 19) (slot 14), .sub (slot 19) (slot 19) (slot 15), .mul (slot 3) (slot 20) (slot 19),
  .mul (slot 20) (slot 12) (slot 18), .sub (slot 19) (slot 15) (slot 14), .mul (slot 4) (slot 20) (slot 19),
  .mul (slot 5) (slot 17) (slot 18)]

/-- `T` (slots 3–5) into `Q` (slots 0, 21, 2). -/
def vtake : List Op := [.copy (slot 0) (slot 3), .copy (slot 21) (slot 4), .copy (slot 2) (slot 5)]

/-! ### `k`'s digits

`k`'s 456 bits are recoded in place, from the lowest, into 456 digits, each zero or odd and
below 16, that sum to `k` weighted by the powers of two: a set bit that no window covers opens a
window of four bits there, whose digit is those bits' value, and the other three digits of the
window are zero. Byte `t` at `VBITS`, the bit of `S` plus twice the bit of `k`, becomes the bit
of `S` plus twice the digit. The recoding reads one bit a step (`recBit`): `r11` counts the bits
read, `r8` holds the weight of the next bit in the window in hand (zero with none: 2, 4, 8 and
then none again), `r7` the byte of that window's digit so far and `r5` the address of that
byte, less `VBITS`. With no window, the bit is the digit, so the byte stays, and opens a window
if it is set; with one, the digit is zero and the bit, at its weight, is added to the window's
digit, whose byte is stored again: the bytes below the bits read are those of their digits, and
nothing is left to do after the last. `k` is public, and so are the digits. -/

/-- The address of byte `r11`, less `VBITS`, into `r3`, the byte (the bit of `S`, plus twice
that of `k`) into `r1`, and Z set with no window in hand. -/
def recHead : List Instr :=
  [.dp .add .r3 .r0 (.reg .r11), .ldrb .r1 .r3 VBITS, .cmp .r8 (.imm 0)]

/-- No window in hand: the bit of `k` is the digit, so the byte stays; it is a window's first,
with the weight 2 next, if it is set. -/
def recOpen : List Instr := [.mov .r7 (.reg .r1), .dp .and .r8 .r1 (.imm 2), .mov .r5 (.reg .r3)]

/-- A window in hand: the digit is zero, so the byte keeps the bit of `S` alone, and the bit of
`k` is added to the window's digit at the weight `r8` (to its byte, at twice that), which
doubles, and is none after 8. -/
def recGrow : List Instr :=
  [.dp .and .r2 .r1 (.imm 1), .strb .r2 .r3 VBITS, .mov .r2 (.shifted .r1 .lsr 1),
    .dp .sub .r2 .r2 (.imm 1), .dp .bic .r2 .r8 (.reg .r2), .dp .add .r7 .r7 (.shifted .r2 .lsl 1),
    .strb .r7 .r5 VBITS, .mov .r8 (.shifted .r8 .lsl 1), .dp .and .r8 .r8 (.imm 15)]

/-- The next bit; Z is set after bit 455. -/
def recNext : List Instr := [.dp .add .r11 .r11 (.imm 1), .cmp .r11 (.imm 456)]

/-- One bit, of byte `r11`. -/
def recBit : Prog isa :=
  .seq (.block recHead) (.seq (.ite .eq (.block recOpen) (.block recGrow)) (.block recNext))

/-- No bit read, no window, and a window's address that is in the bytes. -/
def recInit : List Instr := [.mov .r11 (.imm 0), .mov .r8 (.imm 0), .mov .r5 (.reg .r0)]

/-- `k`'s digits in place of its bits, in the bytes at `VBITS`. -/
def vrecode : Prog isa := .seq (.block recInit) (.loop recBit .ne)

/-! ### The table of `-A`'s odd multiples -/

/-- The table of `[1](-A), [3](-A), …, [15](-A)` in the working space, above the field
functions': 384 bytes an entry, its `X`, `Y` and `Z` 128 bytes apart. -/
def VTAB : Nat := 4096

/-- The limbs of the slot at `a` to the twenty-eight words at `r12 + o`. -/
def toEntry (o a : Nat) : List Instr :=
  (List.range 28).flatMap fun i => [ld .r3 (a + 4 * i), .str .r3 .r12 (o + 4 * i)]

/-- The twenty-eight words at `r12 + a` to the limbs of the slot at `o`. -/
def fromEntry (o a : Nat) : List Instr :=
  (List.range 28).flatMap fun i => [.ldr .r3 .r12 (a + 4 * i), st .r3 (o + 4 * i)]

/-- `Q` (slots 0, 21, 2) to the entry at byte `r11` of the working space; then `r11` moved to the
next entry, and Z set after the last. -/
def ventryStore : List Instr :=
  [.dp .add .r12 .r0 (.reg .r11)] ++ toEntry 0 (slot 0) ++ toEntry 128 (slot 21) ++ toEntry 256 (slot 2) ++
    [.dp .add .r11 .r11 (.imm 384), .movw .r3 (BitVec.ofNat 16 (VTAB + 8 * 384)), .cmp .r11 (.reg .r3)]

/-- `Q = -A` (slots 6, 7 and 10, whose `Z` is 1) and its copy with `Z` in slot 1. -/
def vtableQ : List Op :=
  [.copy (slot 0) (slot 6), .copy (slot 21) (slot 7), .copy (slot 2) (slot 10), .copy X2 (slot 10)]

/-- `Q = -A`, the table's first entry, and `[2](-A)` in slots 6, 7 and 1. -/
def vtableInit (u : Bool) : Prog isa :=
  .seq (ops u vtableQ) <|
  .seq (.block ([.movw .r11 (BitVec.ofNat 16 VTAB)] ++ ventryStore)) (ops u (doubleAt 6 7 1))

/-- The next entry: `Q = Q + [2](-A)`, stored. -/
def vtableStep (u : Bool) : Prog isa := .seq (ops u (addAt 6 7 1 ++ vtake)) (.block ventryStore)

/-- `Q` the neutral point `(0 : 1 : 1)` again, from the 1 in slot 10. -/
def vneutral : List Op :=
  [.sub (slot 0) (slot 0) (slot 0), .copy (slot 21) (slot 10), .copy (slot 2) (slot 10)]

/-- Entries `m < 8` of the table at `VTAB` are `[2m + 1](-A)`, for `-A` in slots 6, 7 and 10; `Q`
is the neutral point after it, as before. -/
def vtable (u : Bool) : Prog isa :=
  .seq (vtableInit u) <| .seq (.loop (vtableStep u) .ne) (ops u vneutral)

/-! ### The sum -/

/-- The counter moved down to the bit `t = r11`, and the byte of bit `t` of `S` (its bit 0) and
of digit `t` of `k` (above it) into `r8`. -/
def vload : List Instr :=
  [.dp .sub .r11 .r11 (.imm 1), .dp .add .r7 .r0 (.reg .r11), .ldrb .r8 .r7 VBITS]

/-- The digit of `k` in `r8` (above its bit 0) into `r3`, and `Z` clear exactly when it is not
zero. -/
def vtest : List Instr := [.mov .r3 (.shifted .r8 .lsr 1), .cmp .r3 (.imm 0)]

/-- `r12` = the address of the entry of the odd digit `r3`, entry `(r3 - 1) / 2`: 192 bytes a
unit of the digit, from `VTAB - 192`. -/
def ventryAddr : List Instr :=
  [.movw .r12 (BitVec.ofNat 16 (VTAB - 192)), .dp .add .r12 .r12 (.shifted .r3 .lsl 7),
    .dp .add .r12 .r12 (.shifted .r3 .lsl 6), .dp .add .r12 .r0 (.reg .r12)]

/-- The entry of the odd digit `r3` into slots 6, 7 and 1. -/
def ventryLoad : List Instr :=
  ventryAddr ++ fromEntry (slot 6) 0 ++ fromEntry (slot 7) 128 ++ fromEntry X2 256

/-- `Q = Q +` the table's entry of the digit of `k` in `r8`, if the digit is not zero. -/
def vaddIf (u : Bool) : Prog isa :=
  .seq (.block vtest)
    (.ite .ne (.seq (.block ventryLoad) (ops u (addAt 6 7 1 ++ vtake))) (.block []))

/-- `Z` clear exactly when `r11 < 114`: the bit is a row of the comb. -/
def vrowTest : List Instr :=
  [.dp .sub .r3 .r11 (.imm 114), .mov .r3 (.shifted .r3 .lsr 31), .cmp .r3 (.imm 0)]

/-- The index of row `t = r11` of the comb of `S` into `r5` (`combDigit`): bits `t`, `t + 114`,
`t + 228` and `t + 342` of `S`, each bit 0 of its byte at `VBITS`. -/
def vcombDigit : List Instr :=
  [.dp .add .r7 .r0 (.reg .r11),
    .ldrb .r5 .r7 (VBITS + 342), .dp .and .r5 .r5 (.imm 1),
    .ldrb .r3 .r7 (VBITS + 228), .dp .and .r3 .r3 (.imm 1), .dp .add .r5 .r3 (.shifted .r5 .lsl 1),
    .ldrb .r3 .r7 (VBITS + 114), .dp .and .r3 .r3 (.imm 1), .dp .add .r5 .r3 (.shifted .r5 .lsl 1),
    .ldrb .r3 .r7 VBITS, .dp .and .r3 .r3 (.imm 1), .dp .add .r5 .r3 (.shifted .r5 .lsl 1)]

/-- In the comb's rows, the bits below 114: the table's entry of the row's four bits of `S`
selected into slots 8–9 (`combSelect`) and added to `Q`. -/
def vcombIf (u : Bool) : Prog isa :=
  .seq (.block vrowTest)
    (.ite .ne (.seq (.block (vcombDigit ++ combSelect)) (ops u (addAt 8 9 10 ++ vtake))) (.block []))

/-- A bit, with its byte in `r8`: `Q` doubled, the comb's entry added in the comb's rows, the
entry of `k`'s digit added if the digit is not zero, and the counter compared with zero. -/
def vdoubleAdd (u : Bool) : Prog isa :=
  .seq (ops u (doubleAt 0 21 2)) <| .seq (vcombIf u) <| .seq (vaddIf u) (.block [.cmp .r11 (.imm 0)])

/-- One bit `t = r11 - 1`, from the top. -/
def vstep (u : Bool) : Prog isa := .seq (.block vload) (vdoubleAdd u)

/-- The 456 bits, from 455 down to 0. -/
def vloop (u : Bool) : Prog isa := .seq (.block [.movw .r11 456]) (.loop (vstep u) .ne)

/-! ## The function -/

/-- Bit `j` of the bytes of `S` (in `r3`) and `k` (in `r9`) to `VBITS + j`
from `r7`, as bit 0 and bit 1. -/
def vbitJ (j : Nat) : List Instr :=
  [.mov .r1 (if j = 0 then .reg .r3 else .shifted .r3 .lsr j), .dp .and .r1 .r1 (.imm 1),
    .mov .r4 (if j = 0 then .reg .r9 else .shifted .r9 .lsr j), .dp .and .r4 .r4 (.imm 1),
    .dp .add .r1 .r1 (.shifted .r4 .lsl 1), .strb .r1 .r7 (VBITS + j)]

/-- Byte `r11` of `S` (at `r12 + 57`) and of `k` (at `r2`) expanded to bytes
`VBITS + 8 r11 + j`. -/
def vbitsBody : List Instr :=
  [.dp .add .r7 .r12 (.reg .r11), .ldrb .r3 .r7 57, .dp .add .r7 .r2 (.reg .r11), .ldrb .r9 .r7 0,
    .dp .add .r7 .r0 (.shifted .r11 .lsl 3)] ++
    (List.range 8).flatMap vbitJ ++ [.dp .add .r11 .r11 (.imm 1), .cmp .r11 (.imm 57)]

/-- All 456 bits of `S` and `k`. -/
def vbits : Prog isa := .seq (.block [.mov .r11 (.imm 0)]) (.loop (.block vbitsBody) .ne)

/-- The callee-saved registers saved at the working space (`r3`), the
pointers to `A` and the signature into `r8` and `r12`, the working space into
`r0`, the limb mask into `r6`, and the link register saved at `LR`. -/
def ventry : List Instr :=
  (List.range 8).map (fun i => .str (saved[i]!) .r3 (4 * i)) ++
    [.mov .r8 (.reg .r0), .mov .r10 (.reg .lr), .mov .r0 (.reg .r3), .movw .r6 65535,
      .mov .r12 (.reg .r1), st .lr LR]

/-- `BAD = 0`, the check of `S`, and the slots initialized as for base-point
multiplication, with `Q`'s `Y` (1) in slot 21. -/
def vstart : List Instr := [.mov .r10 (.imm 0)] ++ sCheck ++ initSlots ++ copy (slot 21) X2

/-- `Q` (slots 0, 21 and 2) and `R` (slots 8–10) doubled twice: a loop of two
iterations, counted by `r11`, each doubling both. -/
def vdouble (u : Bool) : Prog isa :=
  .seq (.block [.movw .r11 2])
    (.loop (.seq (ops u (doubleAt 0 21 2 ++ doubleAt 8 9 10))
      (.block [.dp .sub .r11 .r11 (.imm 1), .cmp .r11 (.imm 0)])) .ne)

/-- One decoding, of the point at `r12` into slots 6–7 (which `decode` reads only before its first
call), after slots 6–7 are kept at `RX` and `RY`; then `r12 := r8`, `r8 := r0`, and `Z` set
exactly when `r8` was the working space. -/
def vdecodeBody (u : Bool) : Prog isa :=
  .seq (.block (copy RX (slot 6) ++ copy RY (slot 7))) <| .seq (decode u .r12 6 7) <|
    .block [.mov .r12 (.reg .r8), .mov .r11 (.reg .r8), .mov .r8 (.reg .r0), .subs .r11 .r11 (.reg .r0)]

/-- `R` (at `r12`) decoded, then `A` (at `r8`, which the field arithmetic preserves): one copy of
`decode`, in a loop whose first pass moves `A`'s pointer into `r12` and the working space's into
`r8`, which is not the working space before it (`A` lies outside it) and is after: `Z` ends the
loop after the second. `A` ends in slots 6–7 and `R` at `RX` and `RY`. -/
def vdecode (u : Bool) : Prog isa := .loop (vdecodeBody u) .ne

/-- `R` into slots 8–9 (`B` is no longer needed). -/
def vR : List Instr := copy (slot 8) RX ++ copy (slot 9) RY

/-- One comparison: slot 0 times slot 10 against slot 8 times slot 2 (`BAD |= 0` exactly when they
are equal); then slots 21 and 9 copied into 0 and 8, for the second pass, and `r11` moved down. -/
def vcmp (u : Bool) : Prog isa :=
  .seq (ops u [.mul (slot 12) (slot 0) (slot 10), .mul (slot 13) (slot 8) (slot 2)]) <|
  .seq (.block (eqSlots (slot 12) (slot 13))) <|
  .seq (ops u [.copy (slot 0) (slot 21), .copy (slot 8) (slot 9)])
    (.block [.dp .sub .r11 .r11 (.imm 1), .cmp .r11 (.imm 0)])

/-- `r0 = (BAD == 0)`, and the callee-saved registers and the link register restored. -/
def vresult : List Instr :=
  [.dp .sub .r1 .r10 (.imm 1), .mov .r1 (.shifted .r1 .lsr 31)] ++
    (List.range 8).map (fun i => ld (saved[i]!) (4 * i)) ++ [ld .lr LR, .mov .r0 (.reg .r1)]

/-- `[4]Q` and `[4]R` compared (`BAD |= 0` exactly when they are the same
point): `X_Q Z_R = X_R Z_Q`, then `Y_Q Z_R = Y_R Z_Q`, by two passes of `vcmp`,
counted by `r11`; then `vresult`. -/
def vfinish (u : Bool) : Prog isa :=
  .seq (vdouble u) <| .seq (.block [.movw .r11 2]) <| .seq (.loop (vcmp u) .ne) (.block vresult)

/-- What comes before `k`'s digits, the table and the loop over the bits: the entry, the bits of
`S` and `k`, the check of `S`, `R` and `A` decoded, and `A` negated. -/
def vbefore (u : Bool) : Prog isa :=
  .seq (.block ventry) <| .seq vbits <| .seq (.block vstart) <| .seq (vdecode u) <|
    ops u [.sub (slot 6) (slot 0) (slot 6)]

/-- What comes after it: `R` into slots 8–9, and the comparison. -/
def vafter (u : Bool) : Prog isa := .seq (.block vR) (vfinish u)

/-- `vg_ed448_verify_equation(pk = r0, signature = r1, challenge = r2, scratch = r3) -> r0`. -/
def verifyEquation (u : Bool) : Prog isa :=
  .seq (vbefore u) <| .seq vrecode <| .seq (vtable u) <| .seq (vloop u) (vafter u)

end VG.Impl.Ed448.Arm
