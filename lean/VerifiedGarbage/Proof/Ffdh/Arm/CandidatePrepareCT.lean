module

import VerifiedGarbage.Proof.Ffdh.Arm.CandidatePrepare
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.NormalizedPrepareCT
import VerifiedGarbage.Proof.Ffdh.Arm.PrepareCT
import VerifiedGarbage.Proof.Bignum.Arm.InlineMontgomery
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Impl.Ffdh.Arm.CandidatePrepare
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Impl.Ffdh.Arm.CandidatePrepare
public import VerifiedGarbage.Proof.Ffdh.Arm.Prepare
meta import VerifiedGarbage.Proof.Ffdh.Arm.Prepare

/-! Fast setup chooses its branch from the public byte count. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

def CandidatePrepareInput (base src : BitVec 32) (len k : Nat) (s : State) : Prop :=
  PrepareInput base src len k s ∧
    (k % 8 = 1 ∨ 2 ^ (64 * (Spec.Rsa.modulusWords k - 1)) ≤
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k))

theorem candidatePrepare_ct {base src : BitVec 32} {len k : Nat} :
    RelCT isa (fun s t => CandidatePrepareInput base src len k s ∧ CandidatePrepareInput base src len k t ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.CandidatePrepare.code (fun _ _ => True) := by
  let E := CandidatePrepareInput base src len k
  let C := fun s : State => E s ∧ s.z = decide (k % 8 = 1)
  have head : RelCT isa (fun s t => E s ∧ E t ∧ s.sp = t.sp)
      (.block VG.Impl.Ffdh.Arm.CandidatePrepare.choose) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r6]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.1.1.count.trans h.2.1.1.count.symm
  have post (s : State) (h : E s) :
      WP isa (.block VG.Impl.Ffdh.Arm.CandidatePrepare.choose) s C := by
    refine WP.mono (candidatePrepareChoice_ok s h.1 h.2) ?_
    rintro t ⟨input,norm,z,_,_⟩
    exact ⟨⟨input,norm⟩,z⟩
  have branch : RelCT isa (fun s t => C s ∧ C t ∧ s.sp = t.sp)
      (.ite .eq VG.Impl.Ffdh.Arm.prepare
        (VG.Impl.Ffdh.Arm.NormalizedPrepare.code VG.Impl.Bignum.Arm.montOp))
      (fun _ _ => True) := by
    refine RelCT.ite (fun s t h => by change some s.z = some t.z;rw [h.1.2,h.2.1.2]) ?_ ?_
    · intro s t trS trT u v h eS eT
      have countFits : 128 * Spec.Rsa.modulusWords k < 2 ^ 32 := by
        have := h.1.1.1.1.maxLength
        dsimp only [Spec.Rsa.modulusWords]
        omega
      exact prepare_ct countFits _ _ _ _ _ _
        ⟨h.1.1.1.1,h.1.2.1.1.1,h.1.2.2⟩ eS eT
    · intro s t trS trT u v h eS eT
      have notBoundary : k % 8 ≠ 1 := by
        have hz : s.z = false := Option.some.inj h.2
        rw [h.1.1.2] at hz
        exact of_decide_eq_false hz
      have fit : Proof.Rsa.Mont.arrAt (Spec.Rsa.modulusWords k) 3 + 32 ≤ 8 * len := by
        have := h.1.1.1.1.space
        simp only [Spec.Rsa.publicScratchWords] at this
        simp only [Proof.Rsa.Mont.arrAt,Proof.Rsa.Mont.hdrBytes]
        omega
      have countFits : 128 * Spec.Rsa.modulusWords k < 2 ^ 32 := by
        have := h.1.1.1.1.maxLength
        dsimp only [Spec.Rsa.modulusWords]
        omega
      exact normalizedPrepare_ct (inlineMontgomery base len (Spec.Rsa.modulusWords k))
        (inlineMontgomery_ct fit) countFits _ _ _ _ _ _
        ⟨⟨h.1.1.1.1,trivial,h.1.1.1.2.resolve_left notBoundary⟩,
          ⟨h.1.2.1.1.1,trivial,h.1.2.1.1.2.resolve_left notBoundary⟩,h.1.2.2⟩ eS eT
  unfold VG.Impl.Ffdh.Arm.CandidatePrepare.code
  exact relCT_chain head post post branch

end VG.Proof.Ffdh.Arm
