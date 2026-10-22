module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.Exponent
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Workspace
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ArithmeticTimingState
meta import VerifiedGarbage.Impl.Dsa.X86.Generation.Exponent
meta import VerifiedGarbage.Impl.Dsa.X86.Generation.Workspace
meta import VerifiedGarbage.Proof.Dsa.X86.Generation.ArithmeticTimingState
meta import VerifiedGarbage.Proof.Framework.X86.Taint

/-! Window alignment uses secret masks and public-width arithmetic loops. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86

private theorem certificate : ∃ hc,
    (VG.Taint.check taint arithmeticTaint
      (Impl.Dsa.X86.Generation.prepareExponent Impl.Dsa.X86.Generation.arithmeticLay) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem prepare_exponent_ct : RelCT isa (VG.X86.Taint.Agree arithmeticTaint)
    (Impl.Dsa.X86.Generation.prepareExponent Impl.Dsa.X86.Generation.arithmeticLay) (fun _ _ => True) := by
  obtain ⟨hc, checked⟩ := certificate
  exact RelCT.taint (A := taint) arithmeticTaint (fun _ _ h => h) checked

end VG.Proof.Dsa.X86.Generation
