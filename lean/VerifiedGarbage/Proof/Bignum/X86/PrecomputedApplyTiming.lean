module

public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedInputTiming
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedDataTiming
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedExportTiming
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedPrepared
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedAcceptance

/-! # Packed-key exponentiation and release do not branch on the representative -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86.Dynamic VG.Proof.Dsa.X86
open VG.Impl.Bignum.X86

def PackedAccepted (base : Addr) (n : Nat) (s : State) : Prop :=
  PublicContext.precomputedAccepted (wordsVal s.mem base (VG.Impl.Bignum.X86.PublicContext.slot n 0) n)
    (wordsVal s.mem base (VG.Impl.Bignum.X86.PublicContext.slot n 5) n) = true

theorem precomputedApply_relCT (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) :
    RelCT isa (fun s t => PrecomputedPair base bytes len args s t ∧
      PackedAccepted base (Spec.Rsa.modulusWords len) s ∧ PackedAccepted base (Spec.Rsa.modulusWords len) t)
      (PrecomputedFn.applyInput (Spec.Rsa.modulusWords len)) (fun _ _ => True) := by
  have Prepare : RelCT isa (PrecomputedPair base bytes len args)
      (.seq (PrecomputedFn.importInput (Spec.Rsa.modulusWords len)) (PrecomputedFn.acceptAndPower (Spec.Rsa.modulusWords len)))
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
    apply VG.RelCT.seq (precomputedInput_relCT base bytes len args)
    apply (precomputedAcceptAndPower_relCT (Spec.Rsa.modulusWords len)).mono
    · intro s t H
      exact agree_regs (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact H.agree.rf.1 _ (by decide))
    · exact fun _ _ h => h
  apply VG.RelCT.assoc
  intro s t tr ur sf tf ⟨H, As, At⟩ E F
  have Fs := of_decide_eq_true As
  have Ft := of_decide_eq_true At
  cases E with
  | seq E1 E2 =>
    cases F with
    | seq F1 F2 =>
      have T1 := (Prepare _ _ _ _ _ _ H E1 F1).1
      obtain ⟨Is, SPs, a, Ms⟩ := wp_result (PublicContext.precomputedPrepared_ok H.left rfl rfl rfl Fs.1 Fs.2.2 Fs.2.1) E1
      obtain ⟨It, SPt, b, Mt⟩ := wp_result (PublicContext.precomputedPrepared_ok H.right rfl rfl rfl Ft.1 Ft.2.2 Ft.2.1) F1
      have Next : PrecomputedPair base bytes len args _ _ := ⟨Is, It, SPs.trans (H.sp.trans SPt.symm)⟩
      have T2 := precomputedExportResult_trace Next H.left.dimensions.1 H.left.space a b Ms Mt E2 F2
      exact ⟨by rw [T1, T2], trivial⟩

end VG.Proof.Bignum.X86
