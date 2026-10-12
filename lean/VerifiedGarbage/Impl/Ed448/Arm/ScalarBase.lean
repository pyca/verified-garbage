module

public import VerifiedGarbage.Impl.X448.Arm
public import VerifiedGarbage.Spec.Ed448

/-!
# Ed448 base-point multiplication on ARMv7

`vg_ed448_scalar_base(out = r0, scalar = r1, scratch = r2)`: the encoding
of `[s]B` for the 456-bit little-endian scalar `s`, without pruning.

Field elements are X448's on this target (twenty-eight 16-bit limbs in the
128-byte slots of the working space, `Impl/X448/Arm.lean`), and so is the
field arithmetic: multiplications (and squarings, as multiplications of a
slot by itself), additions and subtractions (calls of the `vg_gf448_r16_*`
functions), the constant-time swap, the inversion, the full reduction of
slot 1 and its output. Points are the specification's projective
coordinates `(X : Y : Z)`. As in X448, `r0` holds the working space, `r6`
the limb mask, `r8` the output's address and `r10` the link register; the
callee-saved registers are saved in the working space's first 32 bytes.

Every slot is initialized: `R` (slots 0–2) to the neutral point
`(0 : 1 : 1)`, `Q` (slots 8–10) to the base point, slot 11 to `d`, and the
others to zero. The scalar's bits are expanded into bytes at `BITS` (byte
`t` is bit `t`), as X448 expands its scalar. Then, from the top bit down,
`R` is doubled (RFC 8032 §5.2.4's doubling formulas), `T = R + Q` computed
into slots 3–5 (§5.2.4's addition), and `T` swapped into `R` with the mask
of the bit: the same operations for every bit, whatever its value. Finally
`R` is encoded (§5.2.2): `Z` inverted, `y = Y/Z` and `x = X/Z` (into slot
1) fully reduced, the low bit of `x` kept in `r9`, and `y` written as the
output's first 56 bytes and the bit as the top bit of its 57th.

The only branches are on the loop counters, and every address is a pointer
plus a constant or a counter, so only the pointers can affect timing.
-/

@[expose] public section

namespace VG.Impl.Ed448.Arm

open VG.Arm
open VG.Impl.X448.Arm (slot BITS X2 saved ld st Op ops cswap freeze packLimb invert)

/-! ## Initial slots -/

/-- The initial value of slot `i`: `R = (0 : 1 : 1)`, `Q` the base point and
`d`, and zero elsewhere. -/
def initVal (i : Nat) : Nat :=
  if i = 0 then Spec.Ed448.identity.X.val
  else if i = 1 then Spec.Ed448.identity.Y.val
  else if i = 2 then Spec.Ed448.identity.Z.val
  else if i = 8 then Spec.Ed448.basePoint.X.val
  else if i = 9 then Spec.Ed448.basePoint.Y.val
  else if i = 10 then Spec.Ed448.basePoint.Z.val
  else if i = 11 then Spec.Ed448.d.val
  else 0

/-- Limb `k` of slot `i`'s initial value. -/
def initLimb (i k : Nat) : Nat := initVal i / 2 ^ (16 * k) % 65536

/-- Limb `k` of slot `i` (`r4` is zero). -/
def initStep (i k : Nat) : List Instr :=
  if initLimb i k = 0 then [st .r4 (slot i + 4 * k)]
  else [.movw .r3 (BitVec.ofNat 16 (initLimb i k)), st .r3 (slot i + 4 * k)]

def initSlot (i : Nat) : List Instr := (List.range 28).flatMap (initStep i)

/-- Every slot set to its initial value. -/
def initSlots : List Instr := .mov .r4 (.imm 0) :: (List.range 22).flatMap initSlot

/-- The callee-saved registers saved at the working space (`r2`), the
output's address into `r8`, the link register into `r10`, the working space
into `r0`, the limb mask into `r6`, and the slots initialized. -/
def baseEntry : List Instr :=
  .mov .r3 (.reg .r2) :: (List.range 8).map (fun i => .str (saved[i]!) .r3 (4 * i)) ++
    [.mov .r8 (.reg .r0), .mov .r10 (.reg .lr), .mov .r0 (.reg .r3), .movw .r6 65535] ++ initSlots

/-! ## The scalar's bits -/

/-- Bit `j` of the byte in `r3` to `BITS + j` from `r7`. -/
def baseBitJ (j : Nat) : List Instr :=
  [.mov .r2 (if j = 0 then .reg .r3 else .shifted .r3 .lsr j),
    .dp .and .r2 .r2 (.imm 1), .strb .r2 .r7 (BITS + j)]

/-- Byte `r11` of the scalar (at `r1`) expanded to bytes `BITS + 8 r11 + j`. -/
def baseBitsBody : List Instr :=
  [.dp .add .r7 .r1 (.reg .r11), .ldrb .r3 .r7 0, .dp .add .r7 .r0 (.shifted .r11 .lsl 3)] ++
    (List.range 8).flatMap baseBitJ ++ [.dp .add .r11 .r11 (.imm 1), .cmp .r11 (.imm 57)]

/-- All 456 bits of the scalar. -/
def baseBits : Prog isa := .seq (.block [.mov .r11 (.imm 0)]) (.loop (.block baseBitsBody) .ne)

/-! ## The loop over the bits -/

/-- `R = 2R` in slots 0–2 (RFC 8032 §5.2.4, doubling), with the temporaries
12–19: `B = (X + Y)²`, `C = X²`, `D = Y²`, `E = C + D`, `H = Z²`,
`J = E - 2H`, `X = (B - E) J`, `Y = E (C - D)`, `Z = E J`. -/
def doubleOps : List Op := [
  .add (slot 12) (slot 0) (slot 1), .mul (slot 12) (slot 12) (slot 12), .mul (slot 13) (slot 0) (slot 0),
  .mul (slot 14) (slot 1) (slot 1), .add (slot 15) (slot 13) (slot 14), .mul (slot 16) (slot 2) (slot 2),
  .add (slot 17) (slot 16) (slot 16), .sub (slot 17) (slot 15) (slot 17), .sub (slot 18) (slot 12) (slot 15),
  .mul (slot 0) (slot 18) (slot 17), .sub (slot 19) (slot 13) (slot 14), .mul (slot 1) (slot 15) (slot 19),
  .mul (slot 2) (slot 15) (slot 17)]

/-- `T = R + Q` into slots 3–5, for `R` in slots 0–2, `Q` in slots 8–10 and
`d` in slot 11 (RFC 8032 §5.2.4, addition), with the temporaries 12–20:
`A = Z₁Z₂`, `B = A²`, `C = X₁X₂`, `D = Y₁Y₂`, `E = dCD`, `F = B - E`,
`G = B + E`, `H = (X₁ + Y₁)(X₂ + Y₂)`, `X₃ = AF(H - C - D)`,
`Y₃ = AG(D - C)`, `Z₃ = FG`. -/
def addOps : List Op := [
  .mul (slot 12) (slot 2) (slot 10), .mul (slot 13) (slot 12) (slot 12), .mul (slot 14) (slot 0) (slot 8),
  .mul (slot 15) (slot 1) (slot 9), .mul (slot 16) (slot 11) (slot 14), .mul (slot 16) (slot 16) (slot 15),
  .sub (slot 17) (slot 13) (slot 16), .add (slot 18) (slot 13) (slot 16), .add (slot 19) (slot 0) (slot 1),
  .add (slot 20) (slot 8) (slot 9), .mul (slot 19) (slot 19) (slot 20), .mul (slot 20) (slot 12) (slot 17),
  .sub (slot 19) (slot 19) (slot 14), .sub (slot 19) (slot 19) (slot 15), .mul (slot 3) (slot 20) (slot 19),
  .mul (slot 20) (slot 12) (slot 18), .sub (slot 19) (slot 15) (slot 14), .mul (slot 4) (slot 20) (slot 19),
  .mul (slot 5) (slot 17) (slot 18)]

/-- `r5 = -BITS[r11]`: the mask of bit `r11`. -/
def baseMask : List Instr :=
  [.dp .add .r7 .r0 (.reg .r11), .ldrb .r3 .r7 BITS, .mov .r5 (.imm 0), .dp .sub .r5 .r5 (.reg .r3)]

/-- `T` swapped into `R` under the mask of bit `r11`, and the counter
compared with zero. -/
def baseSwap : List Instr :=
  baseMask ++ cswap (slot 0) (slot 3) ++ cswap (slot 1) (slot 4) ++ cswap (slot 2) (slot 5) ++
    [.cmp .r11 (.imm 0)]

/-- One bit `t = r11 - 1`, from the top: `R = 2R`, `T = R + Q`, and `T`
swapped into `R` if bit `t` is set. -/
def baseStep : Prog isa :=
  .seq (.block [.dp .sub .r11 .r11 (.imm 1)]) <| .seq (ops doubleOps) <| .seq (ops addOps) (.block baseSwap)

/-- The 456 bits, from 455 down to 0. -/
def baseLoop : Prog isa := .seq (.block [.movw .r11 456]) (.loop baseStep .ne)

/-! ## The encoding -/

/-- The low bit of the fully reduced `x` (slot 1), as bit 7 of `r9`. -/
def signBit : List Instr :=
  [ld .r9 X2, .dp .and .r9 .r9 (.imm 1), .mov .r9 (.shifted .r9 .lsl 7)]

/-- `1/Z` into slot 21, `y = Y/Z` into slot 4 and `x = X/Z` into slot 1; `x`
fully reduced and its low bit kept; `y` copied into slot 1, fully reduced and
written to the output's first 56 bytes, and the bit as the top bit of its
57th; then the link register and the callee-saved registers restored. -/
def baseEncode : Prog isa :=
  .seq invert <| .seq (ops [.mul (slot 4) (slot 1) (slot 21), .mul X2 (slot 0) (slot 21)]) <|
    .block (freeze ++ signBit ++ Impl.X448.Arm.copy X2 (slot 4) ++ freeze ++
      (List.range 28).flatMap packLimb ++ [.strb .r9 .r8 56, .mov .lr (.reg .r10)] ++
      (List.range 8).map fun i => ld (saved[i]!) (4 * i))

/-- `vg_ed448_scalar_base(out = r0, scalar = r1, scratch = r2)`. -/
def scalarBase : Prog isa :=
  .seq (.block baseEntry) <| .seq baseBits <| .seq baseLoop baseEncode

end VG.Impl.Ed448.Arm
