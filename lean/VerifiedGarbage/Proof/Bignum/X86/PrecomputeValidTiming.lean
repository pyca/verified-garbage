module

public import VerifiedGarbage.Proof.Bignum.X86.PrecomputeSizedTiming
import VerifiedGarbage.Proof.Bignum.X86.PrecomputeDispatchTiming
import VerifiedGarbage.Proof.Bignum.X86.PublicControls
import VerifiedGarbage.Proof.Bignum.X86.PublicDispatch
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Width dispatch depends only on the public modulus length -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86

theorem precomputeValid_relCT (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) :
    RelCT isa (PrecomputeValidPair base bytes len args) PrecomputeFn.valid (fun _ _ => True) := by
  let P := fun s t => PrecomputeValidPair base bytes len args s t ∧
    s.gpr .eax = BitVec.ofNat 32 (Spec.Rsa.modulusWords len) ∧
    t.gpr .eax = BitVec.ofNat 32 (Spec.Rsa.modulusWords len)
  have Setup : RelCT isa (PrecomputeValidPair base bytes len args) (.block PublicFn.widthArgs) P := by
    intro s t tr ur sf tf H E F
    have CT : RelCT isa (VG.X86.Taint.Agree argumentTaint) (.block PublicFn.widthArgs)
        (VG.X86.Taint.Agree argumentTaint) := checkedProgramChange (hint := .block []) rfl rfl
    obtain ⟨Ws, Ms, Ks⟩ := wp_result (widthArgs_ok H.1.left.upper
      (by rw [← H.1.left.nLen]; exact (H.1.left.stack 3 (by decide)).readSrc)) E
    obtain ⟨Wt, Mt, Kt⟩ := wp_result (widthArgs_ok H.1.right.upper
      (by rw [← H.1.right.nLen]; exact (H.1.right.stack 3 (by decide)).readSrc)) F
    refine ⟨(CT _ _ _ _ _ _ H.1.agree E F).1,
      ⟨H.1.keep Ks Kt (by decide) (by decide) (by rw [Ms]; exact Outside.refl _ _ _ _)
        (by rw [Mt]; exact Outside.refl _ _ _ _), ?_, ?_, ?_⟩, Ws, Wt⟩
    · rw [Ms]; exact H.2.1
    · rw [Mt]; exact H.2.2.1
    · rw [Ms,Mt];exact H.2.2.2
  refine VG.RelCT.seq Setup ?_
  intro s t tr ur sf tf H E F
  apply precomputeDispatch_relCT PublicFn.widths (Spec.Rsa.modulusWords len) P
    (publicWidths_member H.1.1.left.lower H.1.1.left.upper) (by decide)
    (fun _ _ J => J.2) ?_ ?_ _ _ _ _ _ _ H E F
  · intro s t u v J Ks Kt Ms Mt
    refine ⟨⟨J.1.1.keep Ks Kt (by simp) (by simp) (by rw [Ms]; exact Outside.refl _ _ _ _)
      (by rw [Mt]; exact Outside.refl _ _ _ _), ?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [Ms]; exact J.1.2.1
    · rw [Mt]; exact J.1.2.2.1
    · rw [Ms,Mt];exact J.1.2.2.2
    · rw [Ks.1 _ (by simp)]; exact J.2.1
    · rw [Kt.1 _ (by simp)]; exact J.2.2
  · exact (precomputeSized_relCT base bytes len args).mono (fun _ _ J => J.1) (fun _ _ h => h)

end VG.Proof.Bignum.X86
