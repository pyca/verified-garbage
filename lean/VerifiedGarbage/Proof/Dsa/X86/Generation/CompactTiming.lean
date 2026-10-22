module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.CompactHeader
public import VerifiedGarbage.Impl.Dsa.X86.Generation.CompactInverse
public import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Impl.Dsa.X86.Generation.CompactHeader
meta import VerifiedGarbage.Impl.Dsa.X86.Generation.CompactInverse
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.X86.RelCT

/-! Compact headers depend only on the public workspace address and width. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86
open VG.Impl.Dsa.X86.Generation

private def headerHint : VG.Taint.Hint VG.X86.Taint.T :=
  VG.Taint.hintOf taint (τr [.edi]) (.block (compactHeader 4))

private theorem header_check :
    (VG.Taint.check taint (τr [.edi]) (.block (compactHeader 4)) headerHint).map (taint.le (τr [.edi])) =
      some true := by taint_decide

theorem compact_header_ct (w : Nat) : RelCT isa (VG.X86.Taint.Agree (τr [.edi]))
    (.block (compactHeader w)) (VG.X86.Taint.Agree (τr [.edi])) := by
  exact VG.Proof.Dsa.X86.erased_relCT (.block (compactHeader w)) (.block (compactHeader 4)) headerHint
    (by kernel_rfl) (by decide +kernel) (by decide +kernel) header_check

private theorem inverse_check : ∃ hc,
    (VG.Taint.check taint (τr [.edi]) (.block compactInverse) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem compact_inverse_ct : RelCT isa (VG.X86.Taint.Agree (τr [.edi]))
    (.block compactInverse) (fun _ _ => True) := by
  obtain ⟨hc, checked⟩ := inverse_check
  exact RelCT.taint (A := taint) (τr [.edi]) (fun _ _ h => h) checked

end VG.Proof.Dsa.X86.Generation
