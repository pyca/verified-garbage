module

public import VerifiedGarbage.Impl.MlKem.AArch64.Basic

/-!
# ML-KEM on AArch64: a polynomial between 16-bit and 32-bit coefficients

`widen` copies the polynomial stored with 16-bit coefficients at `x0` to `x1` with 32-bit
ones (each eight coefficients loaded at once, zero-extended by `zip1` and `zip2` with zero);
`narrow` copies the polynomial stored with 32-bit coefficients at `x0` to `x1` with 16-bit
ones (each eight coefficients loaded as two vectors, their low halfwords kept by `uzp1`).
-/

@[expose] public section

namespace VG.Impl.MlKem.AArch64.Widen16

open VG.AArch64

def widenBody : List Instr :=
  [.ldrq .v0 .x0 0, .vop (.perm .zip1 .h8 .v1 .v0 .v29), .vop (.perm .zip2 .h8 .v2 .v0 .v29),
   .strq .v1 .x1 0, .strq .v2 .x1 16, .addImm .x .x0 .x0 16, .addImm .x .x1 .x1 32, .subImm .x .x10 .x10 1]

def widen : Prog isa :=
  .seq (.block [.movz .x .x10 32 0, .vop (.movi0 .v29)]) (.loop (.block widenBody) (.nonzero .x .x10))

def narrowBody : List Instr :=
  [.ldrq .v0 .x0 0, .ldrq .v1 .x0 16, .vop (.perm .uzp1 .h8 .v2 .v0 .v1), .strq .v2 .x1 0,
   .addImm .x .x0 .x0 32, .addImm .x .x1 .x1 16, .subImm .x .x10 .x10 1]

def narrow : Prog isa :=
  .seq (.block [.movz .x .x10 32 0]) (.loop (.block narrowBody) (.nonzero .x .x10))

end VG.Impl.MlKem.AArch64.Widen16
