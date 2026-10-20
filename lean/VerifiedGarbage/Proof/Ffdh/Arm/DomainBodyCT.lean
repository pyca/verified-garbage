module

public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
import VerifiedGarbage.Proof.Ffdh.Arm.Head
import VerifiedGarbage.Proof.Ffdh.Arm.DomainBody
import VerifiedGarbage.Proof.Ffdh.Arm.DomainMainCT
import VerifiedGarbage.Proof.Ffdh.Arm.HeadCT
import VerifiedGarbage.Proof.Ffdh.Arm.BranchCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
public import VerifiedGarbage.Proof.Framework.RelCT

/-! The complete domain-validation body's trace depends only on the public domain. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem domainBody_ct {p : Inputs} {slots : List Nat}
    (stable : stableSlots slots = true) (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) :
    RelCT isa (fun s t => Context p slots s ∧ Context p slots t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.Domain.head VG.Impl.Ffdh.Arm.Domain.CheckDomain.main) (fun _ _ => True) := by
  let Q := fun s : State => Context p (60 :: 56 :: slots) s ∧ s.z = Spec.Rsa.modulusValid p.P p.k
  have wp (s : State) (h : Context p slots s) :
      WP isa (.seq (.block (VG.Impl.Ffdh.Arm.Domain.prepareArgs 24 ++ VG.Impl.Ffdh.Arm.Domain.domainPointers))
        (.block VG.Impl.Bignum.Arm.modulusCheck)) s Q :=
    WP.mono (head_ok s h stable h0 h24 h32) fun _ j => ⟨j.1, j.2.1⟩
  have stable' : stableSlots (60 :: 56 :: slots) = true := by
    change (true && (true && stableSlots slots)) = true
    rw [Bool.true_and, Bool.true_and, stable]
  have gInput (s : State) (h : Context p (60 :: 56 :: slots) s) :
      DomainMainInput p (60 :: 56 :: slots) ((p.dom.drop p.k).take p.k) s := by
    refine ⟨h, h.gBytes, ?_⟩
    rw [p.gLength]
    exact h.toArgumentMemory.domainSliceStack (by have := p.minLength; omega)
      (by rw [p.domainLength]; split <;> omega)
  have branches : RelCT isa (fun s t => Q s ∧ Q t ∧ s.sp = t.sp)
      (.ite .eq VG.Impl.Ffdh.Arm.Domain.CheckDomain.main (VG.Impl.Ffdh.Arm.Domain.ret 0)) (fun _ _ => True) := by
    apply iteKnown_ct (Spec.Rsa.modulusValid p.P p.k) (fun s h => by change some s.z = _; rw [h.2])
    · intro valid
      have facts := VG.Proof.Bignum.valid_facts valid p.minLength
      exact (domainMain_ct stable' (by simp [h0]) (by simp [h24]) (by simp [h28])
        (by simp [h32]) (by simp) (by simp) facts.2.1 facts.1).mono
        (fun s t h => ⟨gInput s h.1.1, gInput t h.2.1.1, h.2.2⟩) (fun _ _ h => h)
    · intro _
      exact (ret_ct 0).mono (fun _ _ _ => trivial) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.Domain.head
  apply RelCT.assoc
  exact relCT_chain (head_ct stable h0 h24 h32) wp wp branches

end VG.Proof.Ffdh.Arm
