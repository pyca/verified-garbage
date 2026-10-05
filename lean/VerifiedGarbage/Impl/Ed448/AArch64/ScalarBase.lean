import VerifiedGarbage.Impl.Ed448.Formulas
import VerifiedGarbage.Impl.X448.AArch64.Base
import VerifiedGarbage.Spec.Ed448

/-!
# Ed448 base-point multiplication on AArch64

`vg_ed448_scalar_base(out = x0, scalar = x1, scratch = x2)`: the encoding
of `[s]B` for the 456-bit little-endian scalar `s`, without pruning.

`[s]B` is X448's fixed-base comb on edwards448 (`Impl/X448/AArch64/Base.lean`),
over all 57 bytes of the scalar: 57 tables (`stepN 57`), the last
`[m · 256^56] B`, and both accumulators starting at `[G] B` for
`G = 8 Σ_{j < 57} 256^j` (`baseG57`). The scalar's bits are expanded into
bytes at `BITS` (`bits`), as X448 expands its scalar but without clamping.
Then `R = (X : Y : Z)`, in slots 0–2, is encoded (RFC 8032 §5.2.2): `Z`
inverted (`Fast.invert`, into `T7`), `x = X/Z` fully reduced in `X2` and its
low bit stored as the top bit of the 57th byte, and `y = Y/Z` written to
the first 56 as X448 writes its result (`Fast.finish`, which restores the
callee-saved registers).

The field operations are those of `Impl/Curve448/AArch64/Fast.lean`; the
function saves `x19`–`x28` and `v8`–`v15` in the working space and restores
them. The only branches are on the counters, and every address is a pointer
plus a constant or a counter, so only the pointers can affect timing.
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

/-! ## The encoding -/

/-- With `1/Z` in `T7`: `Y` kept in slot 3, and `x = X/Z` into `X2` (slot 1),
fully reduced; its low bit, as the top bit of the output's 57th byte; then `Y`
back in `X2`. -/
def sign : List Instr :=
  .addImm .x .x1 .x20 0 ::
    Impl.X448.AArch64.Fast.codeOf [.copy (slot 3) X2, .mul X2 (slot 0) Impl.X448.AArch64.T7] ++
    Curve448.AArch64.toLegacy X2 ++ Impl.X448.AArch64.freeze ++
    [ld .x4 X2, .lsl .x .x4 .x4 63, .lsr .x .x4 .x4 56, .strb .x4 .x1 56] ++
    Impl.X448.AArch64.Fast.codeOf [.copy X2 (slot 3)]

/-- `Z` (slot 2) inverted into `T7`, the sign of `x`, and `y = Y/Z` written as
X448 writes its result, the registers restored. -/
def encode : Prog isa :=
  .seq Impl.X448.AArch64.Fast.invert <| .seq (.block sign) Impl.X448.AArch64.Fast.finish

/-! ## The function -/

/-- X448's comb's `entry`, the scalar's bits, and both accumulators at `[G] B`. -/
def baseSetup : Prog isa :=
  .seq (.block Impl.X448.AArch64.Base.entry) <| .seq bits <|
    .block (Impl.X448.AArch64.Base.accs Impl.X448.baseG57)

def scalarBase : Prog isa :=
  .seq baseSetup <| .seq (.loop (Impl.X448.AArch64.Base.stepN 57) (.nonzero .x .x9)) <|
    .seq Impl.X448.AArch64.Base.combine encode

end VG.Impl.Ed448.AArch64
