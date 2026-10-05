import VerifiedGarbage.Proof.X448.AArch64.Base.Erase
import VerifiedGarbage.Impl.Ed448.AArch64.ScalarBase

/-!
# Ed448 base-point multiplication on AArch64: the code without its immediates

Untrusted: everything here is checked by Lean. As X448's comb's
(`Proof/X448/AArch64/Base/Erase.lean`): the constant-time analysis and
`noFrames` do not read the immediates of `movz` and `movk` (`Code.eraseImm`),
and without them the selections from the 57 tables are the same code, table
0's (`scalarBase_eraseImm`, proven without evaluating them).
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Proof.X448.AArch64.Base (stepN0 stepN_eraseImm)

/-- `scalarBase`, with every table's selection table 0's. -/
def scalarBase0 : Prog isa :=
  .seq baseSetup <| .seq (.loop (stepN0 57) (.nonzero .x .x9)) <|
    .seq Impl.X448.AArch64.Base.combine encode

/-- `scalarBase` without its immediates. -/
def scalarBaseErased : Prog isa := Code.eraseImm scalarBase0

theorem scalarBase_eraseImm : Code.eraseImm scalarBase = scalarBaseErased := by
  simp only [scalarBaseErased, scalarBase, scalarBase0, Code.eraseImm, stepN_eraseImm]

end VG.Proof.Ed448.AArch64
