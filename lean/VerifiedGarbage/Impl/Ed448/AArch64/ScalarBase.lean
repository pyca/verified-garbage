import VerifiedGarbage.Impl.Ed448.Formulas
import VerifiedGarbage.Impl.X448.AArch64.Base
import VerifiedGarbage.Spec.Ed448

/-!
# Ed448 base-point multiplication on AArch64

`vg_ed448_scalar_base(out = x0, scalar = x1, scratch = x2)`: the encoding
of `[s]B` for the 456-bit little-endian scalar `s`, without pruning.

Field elements are those of X448's ladder (`Impl/Curve448/AArch64.lean`):
eight 56-bit limbs in each of twenty-two 128-byte slots of the working space,
whose products, sums and differences each take and leave limbs below
`2^56 + 32`, so they chain in any order. Points are the specification's
projective coordinates `(X : Y : Z)`.

The scalar's bits are expanded into bytes at `BITS` (byte `t` is bit `t`),
as X448 expands its scalar. Then, from the top bit down, the point `R`
(slots 0–2, from the neutral point) is doubled and `T = R + B` computed with
RFC 8032 §5.2.4's formulas (`doubleOps` and `addOps`, as on x86-64: `B` in
slots 8–10 and `d` in slot 11), and `T` swapped into `R` with the mask of
the bit: the same operations for every bit, whatever its value. Finally `R`
is encoded (§5.2.2): `Z` inverted with X448's addition chain, `x = X/Z` fully
reduced and its low bit stored as the top bit of the 57th byte, and
`y = Y/Z` fully reduced into the first 56, as X448 writes its result.

`x3` holds the working space, `x20` the output pointer (and `x1` once the
scalar's bits are stored), `x19` the counters, `x12` `2^28 - 1` (for the
full reduction); `x19` and `x20` are saved in the working space and
restored. The only branches are on the counters, and every address is a
pointer plus a constant or a counter, so only the pointers can affect
timing.
-/

namespace VG.Impl.Ed448.AArch64

open VG.AArch64
open VG.Impl.X448.AArch64 (ld st slot BITS X2)

/-! ## Field programs on the slots -/

/-- A field operation (`Impl/Ed448/Formulas.lean`) as X448's. -/
def toOp : FOp → Impl.X448.AArch64.Op
  | .mul o a b => .mul (slot o) (slot a) (slot b)
  | .sqr o a => .mul (slot o) (slot a) (slot a)
  | .add o a b => .add (slot o) (slot a) (slot b)
  | .sub o a b => .sub (slot o) (slot a) (slot b)

def field (ops : List FOp) : Prog isa := Impl.X448.AArch64.Weak.ops (ops.map toOp)

/-! ## Entry -/

/-- `x3` the working space, `x12 = 2^28 - 1`, `x19` and `x20` saved, the
output pointer in `x20`, and every slot zeroed. -/
def entry : List Instr :=
  [.addImm .x .x3 .x2 0, .movz .x .x12 0xffff 0, .movk .x .x12 0x0fff 1,
    st .x19 0, st .x20 8, .addImm .x .x20 .x0 0, .movz .x .x4 0 0] ++
  (List.range 352).map (fun i => st .x4 (slot 0 + 8 * i))

/-- `R` the neutral point `(0 : 1 : 1)` (slot 0 is zero), `B` the base point
`(X : Y : 1)`, and `d`. -/
def baseConsts : List Instr :=
  Impl.X448.AArch64.Base.constSlot (slot 1) 1 ++ Impl.X448.AArch64.Base.constSlot (slot 2) 1 ++
    Impl.X448.AArch64.Base.constSlot (slot 8) Spec.Ed448.basePoint.X ++
    Impl.X448.AArch64.Base.constSlot (slot 9) Spec.Ed448.basePoint.Y ++
    Impl.X448.AArch64.Base.constSlot (slot 10) 1 ++ Impl.X448.AArch64.Base.constSlot (slot 11) Spec.Ed448.d

/-! ## The scalar's bits -/

/-- Scalar byte `x19`, expanded into its eight bits at `BITS + 8 x19`. -/
def bitsBody : List Instr :=
  [.add .x .x11 .x1 .x19, .ldrb .x4 .x11 0,
    .lsl .x .x11 .x19 3, .add .x .x11 .x3 .x11] ++
  (List.range 8).flatMap (fun j =>
    [.lsr .x .x5 .x4 j, .logic .and .x .x5 .x5 .x8, .strb .x5 .x11 (BITS + j)]) ++
  [.addImm .x .x19 .x19 1, .subImm .x .x11 .x19 57]

/-- The 57 bytes' 456 bits; then the output pointer into `x1`. -/
def bits : Prog isa :=
  .seq (.block [.movz .x .x19 0 0, .movz .x .x8 1 0]) <|
  .seq (.loop (.block bitsBody) (.nonzero .x .x11)) (.block [.addImm .x .x1 .x20 0])

/-! ## The loop over the bits -/

/-- `x6 = -BITS[x19]`: the mask of bit `x19`, and the conditional swap of
`T` into `R`. -/
def select : List Instr :=
  [.add .x .x11 .x3 .x19, .ldrb .x4 .x11 BITS, .movz .x .x6 0 0, .sub .x .x6 .x6 .x4] ++
    Curve448.AArch64.cswap (slot 0) (slot 3) ++ Curve448.AArch64.cswap (slot 1) (slot 4) ++
    Curve448.AArch64.cswap (slot 2) (slot 5)

/-- One bit `t = x19 - 1`, from the top: `R = 2R`, `T = R + B`, and `T`
swapped into `R` if bit `t` is set. -/
def step : Prog isa :=
  .seq (.block [.subImm .x .x19 .x19 1]) <| .seq (field doubleOps) <| .seq (field addOps) <|
    .block select

/-- The 456 bits, from 455 down to 0. -/
def mulLoop : Prog isa :=
  .seq (.block [.movz .x .x19 456 0]) (.loop step (.nonzero .x .x19))

/-! ## The encoding -/

/-- With `1/Z` in slot 21: `Y` kept in slot 3, and `x = X/Z` into `X2`
(slot 1), fully reduced; its low bit, as the top bit of the output's 57th
byte. -/
def sign : Prog isa :=
  .seq (Impl.X448.AArch64.Weak.ops [.copy (slot 3) (slot 1), .mul (slot 1) (slot 0) (slot 21)]) <|
    .block (Curve448.AArch64.toLegacy X2 ++ Impl.X448.AArch64.freeze ++
      [ld .x4 X2, .lsl .x .x4 .x4 63, .lsr .x .x4 .x4 56, .strb .x4 .x1 56])

/-- `Z` inverted into slot 21, the sign of `x`, then `Y` back in `X2` and
`y = Y/Z` written as X448 writes its result (`X2` times slot 21, fully
reduced, to the output's first 56 bytes), and `x19` and `x20` restored. -/
def encode : Prog isa :=
  .seq Impl.X448.AArch64.Weak.invert <| .seq sign <|
  .seq (Impl.X448.AArch64.Weak.ops [.copy X2 (slot 3)]) Impl.X448.AArch64.Weak.finish

def scalarBase : Prog isa :=
  .seq (.block (entry ++ baseConsts)) <| .seq bits <| .seq mulLoop encode

end VG.Impl.Ed448.AArch64
