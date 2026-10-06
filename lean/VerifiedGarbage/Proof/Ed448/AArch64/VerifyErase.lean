import VerifiedGarbage.Proof.X448.AArch64.Base.Erase
import VerifiedGarbage.Impl.Ed448.AArch64.VerifyWindow

/-!
# Ed448 verification's equation on AArch64: the code without its immediates

Untrusted: everything here is checked by Lean. As X448's comb's
(`Proof/X448/AArch64/Base/Erase.lean`): the constant-time analysis and
`noFrames` do not read the immediates of `movz` and `movk` (`Code.eraseImm`),
and without them the comb's selections from the 57 tables for `[S]B` are the
same code, table 0's (`verifyEquation_eraseImm`, proven without evaluating
them).
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Proof.X448.AArch64.Base (stepN0 stepN_eraseImm)

/-- `sBase`, with every table's selection table 0's. -/
def sBase0 : Prog isa :=
  .seq (.block (Impl.X448.AArch64.Base.accs Impl.X448.baseG57)) <|
  .seq (.loop (stepN0 57) (.nonzero .x .x9)) Impl.X448.AArch64.Base.combine

/-- `verifyEquation` without its immediates, its phases apart (for the constant-time
analysis of each in a declaration of its own). -/
def verifyEquationErased : Prog isa :=
  .seq (Code.eraseImm wfront) <| .seq (Code.eraseImm table) <| .seq (Code.eraseImm sBase0) <|
  .seq (Code.eraseImm kWindows) <| Code.eraseImm (.block (wcross ++ wfinish))

theorem verifyEquation_eraseImm : Code.eraseImm verifyEquation = verifyEquationErased := by
  simp only [verifyEquationErased, verifyEquation, sBase, sBase0, Code.eraseImm, stepN_eraseImm]

end VG.Proof.Ed448.AArch64
