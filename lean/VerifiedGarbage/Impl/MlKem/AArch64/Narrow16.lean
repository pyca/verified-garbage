module
public import VerifiedGarbage.TCB.AArch64.Isa


/-!
# ML-KEM on AArch64: a polynomial from 32-bit to 16-bit coefficients

`narrow` copies the polynomial stored with 32-bit coefficients at `x0`, each less than `2¹⁶`,
to `x1` with 16-bit ones (each eight coefficients loaded at once, their low halfwords taken by
`uzp1`).
-/

@[expose] public section

namespace VG.Impl.MlKem.AArch64.Narrow16

open VG.AArch64

def narrowBody : List Instr :=
  [.ldrq .v0 .x0 0, .ldrq .v1 .x0 16, .vop (.perm .uzp1 .h8 .v2 .v0 .v1), .strq .v2 .x1 0,
   .addImm .x .x0 .x0 32, .addImm .x .x1 .x1 16, .subImm .x .x10 .x10 1]

def narrow : Prog isa :=
  .seq (.block [.movz .x .x10 32 0]) (.loop (.block narrowBody) (.nonzero .x .x10))

end VG.Impl.MlKem.AArch64.Narrow16
