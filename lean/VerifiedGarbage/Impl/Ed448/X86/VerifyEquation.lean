module

public import VerifiedGarbage.Impl.Ed448.X86.ScalarBase

/-!
# Ed448 verification's equation on x86 (32-bit)

`vg_ed448_verify_equation(pk = [esp + 4], signature = [esp + 8],
challenge = [esp + 12], scratch = [esp + 16]) -> eax`: 1 if the public key
and `R` (the signature's first 57 bytes) decode, `S` (its last 57) is below
`L`, and `[4][S]B = [4]R + [4][k]A` for the 456-bit challenge `k`; 0
otherwise.

Field elements and their arithmetic are X448's on this target, as for
base-point multiplication (`ScalarBase.lean`): twenty-eight 16-bit limbs in
the 128-byte slots of the working space, with `edi` the working space and
`esi` the loop counter; the callee-saved registers are saved in the working
space's first 16 bytes. The point formulas are the shared ones
(`Impl/Ed448/Formulas.lean`).

Everything is computed whatever the inputs, and the checks are accumulated
in the word at `BAD`, which stays 0 exactly when every one passes: each
check ORs into it a word that is 0 if and only if it passes. X448's full
reduction works on slot 1 alone, which comparisons and decoding use.

* The bits: byte `t` at `BITS` is bit `t` of `S`, and byte `t` at `KBITS` bit `t` of `k`, by
  X448's `bitsLoop`; then, once `A` is decoded, the bytes at `KBITS` are recoded in place into
  `k`'s digits (`vrecode`), each zero or odd and below 16, which sum to `k` at the powers of two.
* `S < L`: its byte 56 is 0 and its low 448 bits plus `2^448 - L` (the
  limbs `kLimb` of scalar reduction) do not carry out of 448 bits.
* Decoding a point (RFC 8032 §5.2.3) at `esi` into the slots `xo` and `yo`: the twenty-eight limbs of `y`, which must be below `p`
  (they are equal to their full reduction) with bits 448–454 of the encoding
  0; the sign bit to `SIGN`; `u = y² - 1`, `v = d y² - 1` (`decodeUV`), the
  candidate root `x = u³v (u⁵v³)^((p-3)/4)` (by `root`, X448's addition chain
  until `2^223 - 1`, then 223 squarings), the check `v x² = u`, the check
  that `x = 0` comes with the sign bit 0, and `x` swapped with `-x` by a mask
  if its low bit is not the sign bit.
* `R` and then `A` are decoded into slots 6–7 by one loop (`vdecode`), whose
  pointer and count are words of the working space (`PCUR`, `CNT`), `R` kept
  at `RX` and `RY` (`Z = 1` in slot 10). `A` is negated, its odd multiples
  `[1](-A), [3](-A), …, [15](-A)` are put in a table at `VTAB` (`vtable`), and
  `Q = [S]B + [k](-A)` computed from the top bit down: `Q` (slots 0–2) doubled
  for each of the 456 bits; in the last 114, the rows of base-point
  multiplication's comb (`ScalarBase.lean`), the table's entry of the row's
  four bits of `S` selected into slots 8–9 and added, so that the comb shares
  the doublings; and, where digit `t` of `k` is not zero, the entry of `-A`'s
  table for that digit loaded into slots 6, 7 and 21 and added: a sliding
  window of four bits on `k`, in the same doublings. The signature and the
  challenge are public (a verification may leak its inputs), so the window's
  entry is only added where the digit is not zero, and loaded from the
  digit's address: the branch and the address are on the digit, which is
  loaded again from the working space where it is used.
* `Q`'s `Y` is moved to slot 6 (slot 1 is used to compare), `R` copied
  into slots 8–9 (the comb's entry is no longer needed), `Q` and `R` doubled twice (a
  loop, `vdouble`), and compared: `X_Q Z_R = X_R Z_Q` and `Y_Q Z_R = Y_R Z_Q`, fully reduced.

The result is 1 if `BAD` is 0. Every address depends only on the pointers
and on `k`'s digits, and every branch on the pointers and on the bits of `k`.
-/

@[expose] public section

namespace VG.Impl.Ed448.X86

open VG.X86
open VG.Impl.X448.X86 (at_ sc ld st slot BITS bitsLoop TMP X2 Op ops cswap freeze copy pass sqn T0 T1 T2 T3
  T4 T5 T6 T7 restore)

/-! ## The working space -/

/-- The accumulated checks. -/
def BAD : Nat := 16
/-- The sign bit of the point being decoded. -/
def SIGN : Nat := 20
/-- `R`, decoded first, kept while `A` is decoded and `Q` computed: its `X` and `Y`, above
the field arithmetic's working space. -/
def RX : Nat := 4096
def RY : Nat := 4224
/-- The pointer to the point the decoding loop decodes next, and the decodings left. -/
def PCUR : Nat := 4352
def CNT : Nat := 4356

/-- The bits of `k`, one per byte, and then its digits. -/
def KBITS : Nat := 4608

/-- The table of `[1](-A), [3](-A), …, [15](-A)`, above the digits: 384 bytes an entry, its `X`,
`Y` and `Z` 128 bytes apart. -/
def VTAB : Nat := 5120

/-! ## Checks -/

/-- `BAD |= r`. -/
def orBad (r : Reg) : List Instr := [.alu .or r (.mem (sc BAD)), st r BAD]

/-- `ecx |= ` limb `i` of slot 1 XORed with that of the slot at `a`. -/
def diffLimb (a i : Nat) : List Instr :=
  [ld .eax (X2 + 4 * i), .alu .xor .eax (.mem (sc (a + 4 * i))), .alu .or .ecx (.reg .eax)]

/-- `BAD |= 0` exactly when slot 1 and the slot at `a` have the same limbs. -/
def diffSlot (a : Nat) : List Instr :=
  .mov .ecx (.imm 0) :: (List.range 28).flatMap (diffLimb a) ++ orBad .ecx

/-- `BAD |= 0` exactly when the slots at `a` and `b` hold the same field
element: the one at `a` fully reduced (in slot 1) and copied back, the one at
`b` fully reduced in slot 1, and their limbs compared. -/
def eqSlots (a b : Nat) : List Instr :=
  copy X2 a ++ freeze ++ copy a X2 ++ copy X2 b ++ freeze ++ diffSlot a

/-- Limb `i` of the 56 bytes at `esi + src` into `eax`. -/
def byteLimb (src i : Nat) : List Instr :=
  [.movzx8 .eax (at_ .esi (src + 2 * i)), .movzx8 .edx (at_ .esi (src + 2 * i + 1)),
    .shift .ror .edx 24, .alu .add .eax (.reg .edx)]

/-- The twenty-eight limbs of the 56 bytes at `esi` into the slot at `o`. -/
def loadLimbs (o : Nat) : List Instr :=
  (List.range 28).flatMap fun i => byteLimb 0 i ++ [st .eax (o + 4 * i)]

/-- Limb `i` of `S`'s low 448 bits plus that of `2^448 - L`, into `TMP`. -/
def sLimb (i : Nat) : List Instr :=
  byteLimb 57 i ++ [.alu .add .eax (.imm (BitVec.ofNat 32 (kLimb i))), st .eax (TMP + 4 * i)]

/-- `BAD |= 0` exactly when `S` (the signature's last 57 bytes, at
`esi + 57`) is below `L`: the carry out of 448 bits of its low limbs plus
`2^448 - L`, ORed with its byte 56. -/
def sCheck : List Instr :=
  (List.range 28).flatMap sLimb ++ pass TMP TMP ++
    [.movzx8 .eax (at_ .esi 113), .alu .or .eax (.reg .ebx)] ++ orBad .eax

/-! ## Decoding a point -/

/-- `z^((p-3)/4)` into slot 21 for `z` in slot 12, with the temporaries
14–20: X448's addition chain (`invert`) as far as `z^(2^223 - 1)` (in slot
21) and `z^(2^222 - 1)` (in slot 20), then
`(z^(2^223 - 1))^(2^223) · z^(2^222 - 1)`. -/
def root : Prog isa :=
  .seq (ops [.copy T0 (slot 12)]) <| .seq (sqn T0 1) <|
  .seq (ops [.mul T0 T0 (slot 12), .copy T1 T0]) <|
  .seq (sqn T1 2) <| .seq (ops [.mul T1 T1 T0, .copy T2 T1]) <|
  .seq (sqn T2 4) <| .seq (ops [.mul T2 T2 T1, .copy T3 T2]) <|
  .seq (sqn T3 8) <| .seq (ops [.mul T3 T3 T2, .copy T4 T3]) <|
  .seq (sqn T4 16) <| .seq (ops [.mul T4 T4 T3, .copy T5 T4]) <|
  .seq (sqn T5 32) <| .seq (ops [.mul T5 T5 T4, .copy T6 T5]) <|
  .seq (sqn T6 64) <| .seq (ops [.mul T6 T6 T5]) <|
  .seq (sqn T6 64) <| .seq (ops [.mul T6 T6 T5]) <|
  .seq (sqn T6 16) <| .seq (ops [.mul T6 T6 T3]) <|
  .seq (sqn T6 8) <| .seq (ops [.mul T6 T6 T2]) <|
  .seq (sqn T6 4) <| .seq (ops [.mul T6 T6 T1]) <|
  .seq (sqn T6 2) <| .seq (ops [.mul T6 T6 T0, .copy T7 T6]) <|
  .seq (sqn T7 1) <| .seq (ops [.mul T7 T7 (slot 12)]) <|
  .seq (sqn T7 223) (ops [.mul T7 T7 T6])

/-- The last byte of an encoding: its top bit to `SIGN`, the others in `eax`. -/
def signByte : List Instr :=
  [.movzx8 .eax (at_ .esi 56), .mov .edx (.reg .eax), .shift .shr .edx 7, st .edx SIGN,
    .alu .and .eax (.imm 0x7f)]

/-- The 57 bytes at `esi`: `y`'s limbs into slot `yo`, the sign bit to `SIGN`, and `BAD |= 0`
exactly when bits 448–454 are 0 and `y < p`. -/
def decodeY (yo : Nat) : List Instr :=
  loadLimbs (slot yo) ++ signByte ++ orBad .eax ++ copy X2 (slot yo) ++ freeze ++ diffSlot (slot yo)

/-- `edx = ⋁` the limbs of slot 1. -/
def orLimbs : List Instr :=
  ld .edx X2 :: (List.range 27).flatMap fun i => [.alu .or .edx (.mem (sc (X2 + 4 * (i + 1))))]

/-- The sign, with `-x` in slot 12: `x` fully reduced in slot 1; `BAD |= 0`
exactly when `x ≠ 0` or the sign bit is 0; then `x` swapped with `-x` by the
mask of `x`'s low bit differing from the sign bit. -/
def decodeSign (xo : Nat) : List Instr :=
  copy X2 (slot xo) ++ freeze ++ orLimbs ++
    [.alu .sub .edx (.imm 1), .shift .shr .edx 31, .alu .and .edx (.mem (sc SIGN))] ++ orBad .edx ++
    [ld .eax X2, .alu .and .eax (.imm 1), .alu .xor .eax (.mem (sc SIGN)), .mov .ebx (.imm 0),
      .alu .sub .ebx (.reg .eax)] ++ cswap (slot xo) (slot 12)

/-- Decode the 57 bytes at `esi` into slots `xo` and `yo`. -/
def decode (xo yo : Nat) : Prog isa :=
  .seq (.block (decodeY yo)) <| .seq (field (decodeUV yo xo)) <| .seq root <|
  .seq (field [.mul xo xo 21, .sqr 12 xo, .mul 12 3 12]) <|
  .seq (.block (eqSlots (slot 12) (slot 13))) <|
  .seq (field [.sub 12 xo xo, .sub 12 12 xo]) (.block (decodeSign xo))

/-- After a decoding: `PCUR` at `A` (the first argument), and `CNT` moved down (ZF set at 0). -/
def vnext : List Instr :=
  [.mov .esi (.mem (at_ .esp 4)), st .esi PCUR, ld .ebx CNT, .alu .sub .ebx (.imm 1), st .ebx CNT]

/-- Slots 6–7 kept at `RX` and `RY`, and the pointer at `PCUR` into `esi`. -/
def vbodyA : List Instr := copy RX (slot 6) ++ copy RY (slot 7) ++ [ld .esi PCUR]

/-- One decoding: `vbodyA`, the point at `esi` decoded into slots 6–7, then `vnext`. -/
def vdecodeBody : Prog isa := .seq (.block vbodyA) (.seq (decode 6 7) (.block vnext))

/-- The loop's pointer at `R` (the signature's first half, the second argument), and its count 2. -/
def vdecodeInit : List Instr :=
  [.mov .esi (.mem (at_ .esp 8)), st .esi PCUR, .mov .ebx (.imm 2), st .ebx CNT]

/-- `R` decoded, then `A`: a loop of two iterations, counted by `CNT`. `A` ends in slots 6–7
and `R` at `RX` and `RY`. -/
def vdecode : Prog isa := .seq (.block vdecodeInit) (.loop vdecodeBody .ne)

/-- `R` into slots 8–9 (the comb's entry is no longer needed). -/
def vR : List Instr := copy (slot 8) RX ++ copy (slot 9) RY

/-! ## `[S]B + [k](-A)` -/

/-- `T = Q + (x : y : z)` into slots 3–5 (the addition of `addOps`, with the second point in
slots `x`, `y` and `z`). -/
def addAtZ (x y z : Nat) : List FOp := [
  .mul 12 2 z, .sqr 13 12, .mul 14 0 x, .mul 15 1 y, .mul 16 11 14, .mul 16 16 15,
  .sub 17 13 16, .add 18 13 16, .add 19 0 1, .add 20 x y, .mul 19 19 20, .mul 20 12 17,
  .sub 19 19 14, .sub 19 19 15, .mul 3 20 19, .mul 20 12 18, .sub 19 15 14, .mul 4 20 19,
  .mul 5 17 18]

/-! ### `k`'s digits

`k`'s 456 bits are recoded in place, from the lowest, into 456 digits, each zero or odd and
below 16, that sum to `k` weighted by the powers of two: a set bit that no window covers opens a
window of four bits there, whose digit is those bits' value, and the other three digits of the
window are zero. Byte `t` at `KBITS`, the bit of `k`, becomes the digit. The recoding reads one
bit a step (`recBit`): `esi` counts the bits read, `ebx` holds the weight of the next bit in the
window in hand (zero with none: 2, 4, 8 and then none again), `ecx` that window's digit so far
and `eax` the address of that digit's byte, less `KBITS`. With no window, the bit is the digit,
so the byte stays, and opens a window if it is set; with one, the digit is zero and the bit, at
its weight, is added to the window's digit, whose byte is stored again: the bytes below the bits
read are those of their digits, and nothing is left to do after the last. `k` is public, and so
are the digits. -/

/-- The address of byte `esi`, less `KBITS`, into `ebp`, the byte (the bit of `k`) into `edx`,
and ZF set with no window in hand. -/
def recHead : List Instr :=
  [.mov .ebp (.reg .edi), .alu .add .ebp (.reg .esi), .movzx8 .edx (at_ .ebp KBITS),
    .alu .cmp .ebx (.imm 0)]

/-- No window in hand: the bit of `k` is the digit, so the byte stays; it is a window's first,
with the weight 2 next, if it is set. -/
def recOpen : List Instr :=
  [.mov .ecx (.reg .edx), .mov .ebx (.reg .edx), .alu .add .ebx (.reg .ebx), .mov .eax (.reg .ebp)]

/-- A window in hand: the bit of `k` is added to the window's digit at the weight `ebx` (under
the mask of the bit), the digit of the bit is zero, the window's digit is stored again, and the
weight doubles, and is none after 8. -/
def recGrow : List Instr :=
  [.alu .xor .edx (.imm 0xFFFFFFFF), .alu .add .edx (.imm 1), .alu .and .edx (.reg .ebx),
    .alu .add .ecx (.reg .edx), .mov .edx (.imm 0), .store8 (at_ .ebp KBITS) .dl,
    .store8 (at_ .eax KBITS) .cl, .alu .add .ebx (.reg .ebx), .alu .and .ebx (.imm 15)]

/-- The next bit; ZF is set after bit 455. -/
def recNext : List Instr := [.alu .add .esi (.imm 1), .alu .cmp .esi (.imm 456)]

/-- One bit, of byte `esi`. -/
def recBit : Prog isa :=
  .seq (.block recHead) (.seq (.ite .e (.block recOpen) (.block recGrow)) (.block recNext))

/-- No bit read, no window, and a window's address that is in the bytes. -/
def recInit : List Instr :=
  [.mov .esi (.imm 0), .mov .ebx (.imm 0), .mov .ecx (.imm 0), .mov .eax (.reg .edi)]

/-- `k`'s digits in place of its bits, in the bytes at `KBITS`. -/
def vrecode : Prog isa := .seq (.block recInit) (.loop recBit .ne)

/-! ### The table of `-A`'s odd multiples -/

/-- The limbs of the slot at `a` to the twenty-eight words at `ebp + o`. -/
def toEntry (o a : Nat) : List Instr :=
  (List.range 28).flatMap fun i => [ld .eax (a + 4 * i), .store (at_ .ebp (o + 4 * i)) .eax]

/-- The twenty-eight words at `ebp + a` to the limbs of the slot at `o`. -/
def fromEntry (o a : Nat) : List Instr :=
  (List.range 28).flatMap fun i => [.mov .eax (.mem (at_ .ebp (a + 4 * i))), st .eax (o + 4 * i)]

/-- `Q` (slots 0–2) to the entry at byte `esi` of the working space; then `esi` moved to the next
entry, and ZF set after the last. -/
def ventryStore : List Instr :=
  [.mov .ebp (.reg .edi), .alu .add .ebp (.reg .esi)] ++ toEntry 0 (slot 0) ++ toEntry 128 (slot 1) ++
    toEntry 256 (slot 2) ++
    [.alu .add .esi (.imm 384), .alu .cmp .esi (.imm (BitVec.ofNat 32 (VTAB + 8 * 384)))]

/-- `Q = -A` (slots 6, 7 and 10, whose `Z` is 1) and its copy's `Z` in slot 21. -/
def vtableQ : List Op :=
  [.copy (slot 0) (slot 6), .copy (slot 1) (slot 7), .copy (slot 2) (slot 10), .copy (slot 21) (slot 10)]

/-- `T` (slots 3–5) into `Q` (slots 0–2), after an addition. -/
def addTake (l : List FOp) : Prog isa := ops (l.map toOp ++ takeOps)

/-- `Q = -A`, the table's first entry, and `[2](-A)` in slots 6, 7 and 21. -/
def vtableInit : Prog isa :=
  .seq (ops vtableQ) <|
  .seq (.block ([.mov .esi (.imm (BitVec.ofNat 32 VTAB))] ++ ventryStore)) (field (doubleAt 6 7 21))

/-- The next entry: `Q = Q + [2](-A)`, stored. -/
def vtableStep : Prog isa := .seq (addTake (addAtZ 6 7 21)) (.block ventryStore)

/-- `Q` the neutral point `(0 : 1 : 1)` again, from the 1 in slot 10. -/
def vneutral : List Op :=
  [.sub (slot 0) (slot 0) (slot 0), .copy (slot 1) (slot 10), .copy (slot 2) (slot 10)]

/-- Entries `m < 8` of the table at `VTAB` are `[2m + 1](-A)`, for `-A` in slots 6, 7 and 10; `Q`
is the neutral point after it. -/
def vtable : Prog isa := .seq vtableInit <| .seq (.loop vtableStep .ne) (ops vneutral)

/-! ### The sum -/

/-- CF set exactly when `esi < 114`: the bit is a row of the comb. -/
def vrowTest : List Instr := [.alu .cmp .esi (.imm 114)]

/-- In the comb's rows, the bits below 114: the table's entry of the row's four bits of `S`
selected into slots 8–9 (`combSelect`) and added to `Q`. -/
def vcombIf : Prog isa :=
  .seq (.block vrowTest)
    (.ite .b (.seq (.block (combDigit BITS ++ combSelect)) (addTake addOps)) (.block []))

/-- Digit `esi` of `k` into `ecx`, and ZF clear exactly when it is not zero. -/
def vdigit : List Instr :=
  [.mov .ebp (.reg .edi), .alu .add .ebp (.reg .esi), .movzx8 .ecx (at_ .ebp KBITS),
    .alu .cmp .ecx (.imm 0)]

/-- `ebp` = the address of the entry of the odd digit `ecx`, entry `(ecx - 1) / 2`, less
`VTAB - 192`: 192 bytes a unit of the digit (64 and 128 times it, by rotations). -/
def ventryAddr : List Instr :=
  [.shift .ror .ecx 26, .mov .ebp (.reg .ecx), .shift .ror .ecx 31, .alu .add .ebp (.reg .ecx),
    .alu .add .ebp (.reg .edi)]

/-- The entry of the odd digit `ecx` into slots 6, 7 and 21. -/
def ventryLoad : List Instr :=
  ventryAddr ++ fromEntry (slot 6) (VTAB - 192) ++ fromEntry (slot 7) (VTAB - 192 + 128) ++
    fromEntry (slot 21) (VTAB - 192 + 256)

/-- `Q = Q +` the table's entry of digit `esi` of `k`, if the digit is not zero. -/
def vaddIf : Prog isa :=
  .seq (.block vdigit)
    (.ite .ne (.seq (.block ventryLoad) (addTake (addAtZ 6 7 21))) (.block []))

/-- One bit `t = esi - 1`, from the top: `Q` doubled, the comb's entry added in the comb's rows,
the entry of `k`'s digit added if the digit is not zero, and the counter compared with zero. -/
def vstep : Prog isa :=
  .seq (.block [.alu .sub .esi (.imm 1)]) <| .seq (field doubleOps) <| .seq vcombIf <|
  .seq vaddIf (.block [.alu .cmp .esi (.imm 0)])

/-- The 456 bits, from 455 down to 0. -/
def vloop : Prog isa := .seq (.block [.mov .esi (.imm 456)]) (.loop vstep .ne)

/-! ## The function -/

/-- The bits of `k` (the challenge) at `KBITS` and those of `S` (the signature's last 57 bytes) at
`BITS`, by `bitsLoop`, with the signature's pointer kept in `ebx`; then `esi` back at the
signature. -/
def vbits : Prog isa :=
  .seq (.block [.mov .esi (.mem (at_ .esp 12)), .mov .ebx (.mem (at_ .esp 8))]) <|
  .seq (bitsLoop KBITS 57) <| .seq (.block [.mov .esi (.reg .ebx), .alu .add .esi (.imm 57)]) <|
  .seq (bitsLoop BITS 57) (.block [.alu .sub .esi (.imm 114)])

/-- After the bits: `BAD = 0`, the check of `S`, and the slots initialized as for base-point
multiplication. -/
def vinit : Prog isa := .seq (.block ([.mov .eax (.imm 0), st .eax BAD] ++ sCheck)) initSlots

/-- The callee-saved registers saved, the bits of `S` and `k`, and `vinit`. -/
def ventry : Prog isa := .seq (.block (save 16)) (.seq vbits vinit)

/-- `Q` (slots 0, 6 and 2) and `R` (slots 8–10) doubled twice: a loop of two
iterations, counted by `esi`, each doubling both. -/
def vdouble : Prog isa :=
  .seq (.block [.mov .esi (.imm 2)])
    (.loop (.seq (field (doubleAt 0 6 2 ++ doubleAt 8 9 10)) (.block [.alu .sub .esi (.imm 1)])) .ne)

/-- One comparison: slot 0 times slot 10 against slot 8 times slot 2 (`BAD |= 0` exactly when they
are equal); then slots 6 and 9 copied into 0 and 8, for the second pass, and `esi` moved down. -/
def vcmp : Prog isa :=
  .seq (field [.mul 12 0 10, .mul 13 8 2]) <| .seq (.block (eqSlots (slot 12) (slot 13))) <|
  .seq (ops [.copy (slot 0) (slot 6), .copy (slot 8) (slot 9)]) (.block [.alu .sub .esi (.imm 1)])

/-- `[4]Q` and `[4]R` compared (`Q` in slots 0, 6 and 2, `R` in 8–10;
`BAD |= 0` exactly when they are the same point): `X_Q Z_R = X_R Z_Q`, then
`Y_Q Z_R = Y_R Z_Q`, by two passes of `vcmp`, counted by `esi`; then the
callee-saved registers restored, and `eax = (BAD == 0)`. -/
def vfinish : Prog isa :=
  .seq vdouble <| .seq (.block [.mov .esi (.imm 2)]) <| .seq (.loop vcmp .ne) <|
  .block ([ld .ecx BAD, .alu .sub .ecx (.imm 1), .shift .shr .ecx 31] ++ restore ++ [.mov .eax (.reg .ecx)])

/-- After the decodings: `A` negated, `k`'s digits, the table of `-A`'s odd multiples, `Q`, `R`
copied back, and the comparison. -/
def vafter : Prog isa :=
  .seq (field [.sub 6 0 6]) <| .seq vrecode <| .seq vtable <| .seq vloop <|
  .seq (ops [.copy (slot 6) X2]) <| .seq (.block vR) vfinish

/-- `vg_ed448_verify_equation(pk = [esp + 4], signature = [esp + 8],
challenge = [esp + 12], scratch = [esp + 16]) -> eax`. -/
def verifyEquation : Prog isa := .seq ventry (.seq vdecode vafter)

end VG.Impl.Ed448.X86
