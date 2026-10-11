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

* The bits: byte `t` at `BITS` is bit `t` of `S` plus twice bit `t` of `k`.
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
  at `RX` and `RY` (`Z = 1` in slot 10). `A` is negated; slot 1, `Q`'s `Y`, is
  set to 1 again, and `Q = [S]B + [k](-A)` computed from the
  top bit down, as `[s]B` is: `Q` (slots 0–2) doubled, `B` (slots 8–10) added
  and swapped into `Q` by bit `t` of `S`, then `-A` added and swapped in by
  bit `t` of `k`.
* `Q`'s `Y` is moved to slot 6 (slot 1 is used to compare), `R` copied
  into slots 8–9 (`B` is no longer needed), `Q` and `R` doubled twice (a
  loop, `vdouble`), and compared: `X_Q Z_R = X_R Z_Q` and `Y_Q Z_R = Y_R Z_Q`, fully reduced.

The result is 1 if `BAD` is 0. Every address and branch depends only on the
pointers.
-/

@[expose] public section

namespace VG.Impl.Ed448.X86

open VG.X86
open VG.Impl.X448.X86 (at_ sc ld st slot BITS TMP X2 Op ops cswap freeze copy pass sqn T0 T1 T2 T3
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

/-- `R` into slots 8–9 (`B` is no longer needed). -/
def vR : List Instr := copy (slot 8) RX ++ copy (slot 9) RY

/-! ## `[S]B + [k](-A)` -/

/-- `ebx = -bit`, for bit `esi` of `S` (`hi = false`) or of `k` (`hi = true`). -/
def vmask (hi : Bool) : List Instr :=
  [.mov .ebp (.reg .edi), .alu .add .ebp (.reg .esi), .movzx8 .eax (at_ .ebp BITS),
    if hi then .shift .shr .eax 1 else .alu .and .eax (.imm 1), .mov .ebx (.imm 0),
    .alu .sub .ebx (.reg .eax)]

/-- `T` (slots 3–5) swapped into `Q` (slots 0–2) by the mask `ebx`. -/
def swapT : List Instr :=
  cswap (slot 0) (slot 3) ++ cswap (slot 1) (slot 4) ++ cswap (slot 2) (slot 5)

/-- One bit `t = esi - 1`, from the top. -/
def vstep : Prog isa :=
  .seq (.block [.alu .sub .esi (.imm 1)]) <| .seq (field (doubleAt 0 1 2)) <|
  .seq (field (addAt 8 9)) <| .seq (.block (vmask false ++ swapT)) <|
  .seq (field (addAt 6 7)) (.block (vmask true ++ swapT ++ [.alu .cmp .esi (.imm 0)]))

/-- The 456 bits, from 455 down to 0. -/
def vloop : Prog isa := .seq (.block [.mov .esi (.imm 456)]) (.loop vstep .ne)

/-! ## The function -/

/-- Bit `j` of the bytes of `S` (in `eax`) and `k` (in `ecx`) to
`BITS + 8 i + j`, as bit 0 and bit 1. -/
def vbitJ (i j : Nat) : List Instr :=
  [.mov .edx (.reg .eax)] ++ (if j = 0 then [] else [.shift .shr .edx j]) ++
    [.alu .and .edx (.imm 1), .mov .ebx (.reg .ecx)] ++
    (if j = 0 then [] else [.shift .shr .ebx j]) ++
    [.alu .and .ebx (.imm 1), .alu .add .edx (.reg .ebx), .alu .add .edx (.reg .ebx),
      .store8 (sc (BITS + 8 * i + j)) .dl]

/-- Byte `i` of `S` (at `esi + 57`) and of `k` (at `ebp`) expanded to bytes
`BITS + 8 i + j`. -/
def vbyte (i : Nat) : List Instr :=
  [.movzx8 .eax (at_ .esi (57 + i)), .movzx8 .ecx (at_ .ebp i)] ++ (List.range 8).flatMap (vbitJ i)

/-- All 456 bits of `S` and `k`. -/
def vbits : List Instr :=
  [.mov .esi (.mem (at_ .esp 8)), .mov .ebp (.mem (at_ .esp 12))] ++ (List.range 57).flatMap vbyte

/-- The callee-saved registers saved, the bits of `S` and `k`, `BAD = 0`, the
check of `S`, and the slots initialized as for base-point multiplication. -/
def ventry : List Instr :=
  save 16 ++ vbits ++ [.mov .eax (.imm 0), st .eax BAD] ++ sCheck ++ initSlots

/-- `Q` (slots 0, 6 and 2) and `R` (slots 8–10) doubled twice: a loop of two
iterations, counted by `esi`, each doubling both. -/
def vdouble : Prog isa :=
  .seq (.block [.mov .esi (.imm 2)])
    (.loop (.seq (field (doubleAt 0 6 2 ++ doubleAt 8 9 10)) (.block [.alu .sub .esi (.imm 1)])) .ne)

/-- `[4]Q` and `[4]R` compared (`Q` in slots 0, 6 and 2, `R` in 8–10;
`BAD |= 0` exactly when they are the same point), the callee-saved
registers restored, and `eax = (BAD == 0)`. -/
def vfinish : Prog isa :=
  .seq vdouble <| .seq (field [.mul 12 0 10, .mul 13 8 2]) <|
  .seq (.block (eqSlots (slot 12) (slot 13))) <| .seq (field [.mul 12 6 10, .mul 13 9 2]) <|
  .block (eqSlots (slot 12) (slot 13) ++
    [ld .ecx BAD, .alu .sub .ecx (.imm 1), .shift .shr .ecx 31] ++ restore ++ [.mov .eax (.reg .ecx)])

/-- After the decodings: `A` negated, `Q`, `R` copied back, and the comparison. -/
def vafter : Prog isa :=
  .seq (field [.sub 6 0 6]) <| .seq (ops [.copy X2 (slot 10)]) <| .seq vloop <|
  .seq (ops [.copy (slot 6) X2]) <| .seq (.block vR) vfinish

/-- `vg_ed448_verify_equation(pk = [esp + 4], signature = [esp + 8],
challenge = [esp + 12], scratch = [esp + 16]) -> eax`. -/
def verifyEquation : Prog isa := .seq (.block ventry) (.seq vdecode vafter)

end VG.Impl.Ed448.X86
