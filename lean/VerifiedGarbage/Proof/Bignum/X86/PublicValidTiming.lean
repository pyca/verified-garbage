module

public import VerifiedGarbage.Proof.Bignum.X86.PublicValidSetup
public import VerifiedGarbage.Proof.Bignum.X86.PublicDispatchTiming
public import VerifiedGarbage.Proof.Bignum.X86.PublicSizedTiming

/-! # A validated public modulus fixes the width-dispatch and arithmetic traces -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86

def ValidPair (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (s t : State) : Prop :=
  PublicPair base bytes len args s t ∧
    Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len)) len = true ∧
    Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem (byteAddr (args 2)) len)) len = true

theorem ValidPair.keepMem {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {s t u v : State}
    (H : ValidPair base bytes len args s t) {regs : List Reg}
    (Ks : Keeps regs s u) (Kt : Keeps regs t v) (di : .edi ∉ regs) (sp : .esp ∉ regs)
    (Ms : u.mem = s.mem) (Mt : v.mem = t.mem) : ValidPair base bytes len args u v := by
  refine ⟨H.1.keep Ks Kt di sp (by rw [Ms]; exact Outside.refl _ _ _ _)
    (by rw [Mt]; exact Outside.refl _ _ _ _), ?_, ?_⟩
  · rw [Ms]; exact H.2.1
  · rw [Mt]; exact H.2.2

theorem publicValid_relCT (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) :
    RelCT isa (fun s t => ValidPair base bytes len args s t ∧
        s.gpr .ebx = t.gpr .ebx ∧ s.gpr .edx = t.gpr .edx) PublicFn.valid (fun _ _ => True) := by
  let P := fun s t => (ValidPair base bytes len args s t ∧
      val32 s.mem base 128 2 = val32 t.mem base 128 2) ∧
    s.gpr .eax = BitVec.ofNat 32 (Spec.Rsa.modulusWords len) ∧
    t.gpr .eax = BitVec.ofNat 32 (Spec.Rsa.modulusWords len)
  have Setup : RelCT isa (fun s t => ValidPair base bytes len args s t ∧
        s.gpr .ebx = t.gpr .ebx ∧ s.gpr .edx = t.gpr .edx)
      (.seq (.block PublicFn.saveExponent) (.block PublicFn.widthArgs)) P := by
    intro s t tr ur sf tf ⟨H, Rb, Rd⟩ E F
    have CT : RelCT isa (VG.X86.Taint.Agree argumentTaint)
        (.seq (.block PublicFn.saveExponent) (.block PublicFn.widthArgs)) (VG.X86.Taint.Agree argumentTaint) :=
      checkedProgramChange (hint := .seq argumentTaint (.block []) (.block [])) rfl rfl
    obtain ⟨Is, SPs, Ws, Ns, Xs⟩ := wp_result (publicValidSetup_ok H.1.left) E
    obtain ⟨It, SPt, Wt, Nt, Xt⟩ := wp_result (publicValidSetup_ok H.1.right) F
    exact ⟨(CT _ _ _ _ _ _ H.1.agree E F).1,
      ⟨⟨⟨Is, It, SPs.trans (H.1.sp.trans SPt.symm)⟩, by rw [Ns]; exact H.2.1, by rw [Nt]; exact H.2.2⟩,
        by rw [Xs, Xt, Rb, Rd]⟩, Ws, Wt⟩
  apply VG.RelCT.assoc
  refine VG.RelCT.seq Setup ?_
  intro s t tr ur sf tf H E F
  apply publicDispatch_relCT PublicFn.widths (Spec.Rsa.modulusWords len) P
    (publicWidths_member H.1.1.1.left.lower H.1.1.1.left.upper) (by decide)
    (fun _ _ J => J.2) ?_ ?_ _ _ _ _ _ _ H E F
  · intro s t u v J Ks Kt Ms Mt
    refine ⟨⟨⟨J.1.1.1.keep Ks Kt (by simp) (by simp) (by rw [Ms]; exact Outside.refl _ _ _ _)
      (by rw [Mt]; exact Outside.refl _ _ _ _), ?_, ?_⟩, ?_⟩, ?_, ?_⟩
    · rw [Ms]; exact J.1.1.2.1
    · rw [Mt]; exact J.1.1.2.2
    · rw [Ms, Mt]; exact J.1.2
    · rw [Ks.1 _ (by simp)]; exact J.2.1
    · rw [Kt.1 _ (by simp)]; exact J.2.2
  · exact (publicSized_relCT base bytes len args).mono
      (fun _ _ J => ⟨J.1.1.1, J.1.1.2.1, J.1.1.2.2, J.1.2⟩) (fun _ _ h => h)

end VG.Proof.Bignum.X86
