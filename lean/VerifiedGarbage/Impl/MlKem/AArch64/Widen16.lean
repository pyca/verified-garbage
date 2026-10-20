module
public import VerifiedGarbage.TCB.AArch64.Isa


/-!
# ML-KEM on AArch64: a polynomial from 16-bit to 32-bit coefficients

`widen` copies the polynomial stored with 16-bit coefficients at `x0` to `x1` with 32-bit
ones (each eight coefficients loaded at once, zero-extended by `zip1` and `zip2` with zero).
-/

@[expose] public section

namespace VG.Impl.MlKem.AArch64.Widen16

open VG.AArch64

def widenBody : List Instr :=
  [.ldrq .v0 .x0 0, .vop (.perm .zip1 .h8 .v1 .v0 .v29), .vop (.perm .zip2 .h8 .v2 .v0 .v29),
   .strq .v1 .x1 0, .strq .v2 .x1 16, .addImm .x .x0 .x0 16, .addImm .x .x1 .x1 32, .subImm .x .x10 .x10 1]

def widen : Prog isa :=
  .seq (.block [.movz .x .x10 32 0, .vop (.movi0 .v29)]) (.loop (.block widenBody) (.nonzero .x .x10))

end VG.Impl.MlKem.AArch64.Widen16
