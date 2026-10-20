module
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Proof.Bignum.X86.CrtPair
public import VerifiedGarbage.Spec.Weierstrass.Point
public import VerifiedGarbage.Impl.Bignum.X86.CrtFn

import VerifiedGarbage.Proof.Bignum.X86.CrtDispatchTiming
import VerifiedGarbage.Proof.Bignum.X86.CrtSizedTiming
import VerifiedGarbage.Proof.Bignum.X86.PublicControls
import VerifiedGarbage.Proof.Bignum.X86.PublicDispatch
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Width selection and CRT dispatch depend only on public arguments -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86

theorem valid_relCT (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) :
    RelCT isa (Pair base bytes len args) Crt.valid (fun _ _ => True) := by
  let P := fun s t => Pair base bytes len args s t ∧
    s.gpr .eax = BitVec.ofNat 32 (Spec.Rsa.modulusWords len) ∧
    t.gpr .eax = BitVec.ofNat 32 (Spec.Rsa.modulusWords len)
  have Setup : RelCT isa (Pair base bytes len args) (.block PublicFn.widthArgs) P := by
    intro s t tr ur sf tf H E F
    have CT : RelCT isa (VG.X86.Taint.Agree argumentTaint) (.block PublicFn.widthArgs)
        (VG.X86.Taint.Agree argumentTaint) := checkedProgramChange (hint := .block []) rfl rfl
    obtain ⟨Ws, Ms, Ks⟩ := wp_result (widthArgs_ok H.left.upper
      (by rw [← H.left.nLen]; exact (H.left.stack 3 (by decide)).readSrc)) E
    obtain ⟨Wt, Mt, Kt⟩ := wp_result (widthArgs_ok H.right.upper
      (by rw [← H.right.nLen]; exact (H.right.stack 3 (by decide)).readSrc)) F
    exact ⟨(CT _ _ _ _ _ _ H.agree E F).1,
      H.keep Ks Kt (by decide) (by decide) (by rw [Ms]; exact Outside.refl _ _ _ _)
        (by rw [Mt]; exact Outside.refl _ _ _ _), Ws, Wt⟩
  refine VG.RelCT.seq Setup ?_
  intro s t tr ur sf tf H E F
  apply dispatch_relCT PublicFn.widths (Spec.Rsa.modulusWords len) P
    (publicWidths_member H.1.left.lower H.1.left.upper) (by decide)
    (fun _ _ J => J.2) ?_ ?_ _ _ _ _ _ _ H E F
  · intro s t u v J Ks Kt Ms Mt
    refine ⟨J.1.keep Ks Kt (by simp) (by simp) (by rw [Ms]; exact Outside.refl _ _ _ _)
      (by rw [Mt]; exact Outside.refl _ _ _ _), ?_, ?_⟩
    · rw [Ks.1 _ (by simp)]; exact J.2.1
    · rw [Kt.1 _ (by simp)]; exact J.2.2
  · exact (sized_relCT base bytes len args).mono (fun _ _ J => J.1) (fun _ _ h => h)

end VG.Proof.Bignum.X86.Crt
