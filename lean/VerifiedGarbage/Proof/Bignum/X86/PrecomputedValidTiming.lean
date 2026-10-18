module

public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedValidSetup
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedDispatchTiming
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedCheckedTiming

/-! # A validated public modulus fixes the width-dispatch and arithmetic traces -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86

def PrecomputedValidPair (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (s t : State) : Prop :=
  PrecomputedPair base bytes len args s t ∧
    Spec.Rsa.wordsAt s.mem (byteAddr (args 2)) (2 * Spec.Rsa.modulusWords len) =
      Spec.Rsa.wordsAt t.mem (byteAddr (args 2)) (2 * Spec.Rsa.modulusWords len)

theorem PrecomputedValidPair.keepMem {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {s t u v : State}
    (H : PrecomputedValidPair base bytes len args s t) {regs : List Reg}
    (Ks : Keeps regs s u) (Kt : Keeps regs t v) (di : .edi ∉ regs) (sp : .esp ∉ regs)
    (Ms : u.mem = s.mem) (Mt : v.mem = t.mem) : PrecomputedValidPair base bytes len args u v := by
  refine ⟨H.1.keep Ks Kt di sp (by rw [Ms]; exact Outside.refl _ _ _ _)
    (by rw [Mt]; exact Outside.refl _ _ _ _), ?_⟩
  · rw [Ms, Mt]; exact H.2

theorem precomputedValid_relCT (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) :
    RelCT isa (PrecomputedValidPair base bytes len args) PrecomputedFn.valid (fun _ _ => True) := by
  let P := fun s t => PrecomputedValidPair base bytes len args s t ∧
    s.gpr .eax = BitVec.ofNat 32 (Spec.Rsa.modulusWords len) ∧
    t.gpr .eax = BitVec.ofNat 32 (Spec.Rsa.modulusWords len)
  have Setup : RelCT isa (PrecomputedValidPair base bytes len args)
      (.seq (.block PublicFn.saveExponent) (.block PrecomputedFn.widthArgs)) P := by
    intro s t tr ur sf tf H E F
    have CT : RelCT isa (VG.X86.Taint.Agree argumentTaint)
        (.seq (.block PublicFn.saveExponent) (.block PrecomputedFn.widthArgs)) (VG.X86.Taint.Agree argumentTaint) :=
      checkedProgramChange (hint := .seq argumentTaint (.block []) (.block [])) rfl rfl
    obtain ⟨Is, SPs, Ws, Ns⟩ := wp_result (precomputedValidSetup_ok H.1.left) E
    obtain ⟨It, SPt, Wt, Nt⟩ := wp_result (precomputedValidSetup_ok H.1.right) F
    exact ⟨(CT _ _ _ _ _ _ H.1.agree E F).1,
      ⟨⟨Is, It, SPs.trans (H.1.sp.trans SPt.symm)⟩, by rw [Ns, Nt]; exact H.2⟩, Ws, Wt⟩
  apply VG.RelCT.assoc
  refine VG.RelCT.seq Setup ?_
  intro s t tr ur sf tf H E F
  apply precomputedDispatch_relCT PublicFn.widths (Spec.Rsa.modulusWords len) P
    (publicWidths_member H.1.1.left.lower H.1.1.left.upper) (by decide)
    (fun _ _ J => J.2) ?_ ?_ _ _ _ _ _ _ H E F
  · intro s t u v J Ks Kt Ms Mt
    refine ⟨⟨J.1.1.keep Ks Kt (by simp) (by simp) (by rw [Ms]; exact Outside.refl _ _ _ _)
      (by rw [Mt]; exact Outside.refl _ _ _ _), ?_⟩, ?_, ?_⟩
    · rw [Ms, Mt]; exact J.1.2
    · rw [Ks.1 _ (by simp)]; exact J.2.1
    · rw [Kt.1 _ (by simp)]; exact J.2.2
  · exact (precomputedSized_relCT base bytes len args).mono (fun _ _ J => J.1) (fun _ _ h => h)

end VG.Proof.Bignum.X86
