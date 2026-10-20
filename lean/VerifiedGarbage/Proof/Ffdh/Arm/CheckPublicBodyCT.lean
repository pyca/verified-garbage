module

import VerifiedGarbage.Proof.Ffdh.Arm.Head
public import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicMainCT
import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicBody
import VerifiedGarbage.Proof.Ffdh.Arm.HeadCT
import VerifiedGarbage.Proof.Ffdh.Arm.BranchCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
public import VerifiedGarbage.Proof.Framework.RelCT

/-! The public-value body has a trace determined by its documented public inputs. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem checkPublicBody_ct {p : Inputs} {slots : List Nat} {yb : List Byte}
    (stable : stableSlots slots = true) (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots)
    (h32 : 32 ∈ slots) (h36 : 36 ∈ slots) (length : yb.length = p.k) :
    RelCT isa (fun s t => PublicMainInput p slots yb s ∧ PublicMainInput p slots yb t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.Domain.head VG.Impl.Ffdh.Arm.Domain.CheckPublic.main) (fun _ _ => True) := by
  let Q := fun s : State => PublicMainInput p (60 :: 56 :: slots) yb s ∧ s.z = Spec.Rsa.modulusValid p.P p.k
  have head := (head_ct stable h0 h24 h32).mono
    (P' := fun (s t : State) => PublicMainInput p slots yb s ∧ PublicMainInput p slots yb t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.context, h.2.1.context, h.2.2⟩) (fun _ _ h => h)
  have wp (s : State) (h : PublicMainInput p slots yb s) :
      WP isa (.seq (.block (VG.Impl.Ffdh.Arm.Domain.prepareArgs 24 ++ VG.Impl.Ffdh.Arm.Domain.domainPointers))
        (.block VG.Impl.Bignum.Arm.modulusCheck)) s Q := by
    refine WP.mono (head_ok s h.context stable h0 h24 h32) ?_
    rintro u ⟨context, zero, frame, rest⟩
    refine ⟨⟨context, h.value.after_frame frame rest (by
      intro r hr
      rw [List.mem_singleton] at hr
      subst r
      exact h.separate), ?_⟩, zero⟩
    rw [rest.sp]; exact h.separate
  have stable' : stableSlots (60 :: 56 :: slots) = true := by
    change (true && (true && stableSlots slots)) = true
    rw [Bool.true_and, Bool.true_and, stable]
  have branches : RelCT isa (fun s t => Q s ∧ Q t ∧ s.sp = t.sp)
      (.ite .eq VG.Impl.Ffdh.Arm.Domain.CheckPublic.main (VG.Impl.Ffdh.Arm.Domain.ret 0)) (fun _ _ => True) := by
    apply iteKnown_ct (Spec.Rsa.modulusValid p.P p.k) (fun s h => by change some s.z = _; rw [h.2])
    · intro valid
      have facts := VG.Proof.Bignum.valid_facts valid p.minLength
      exact (checkPublicMain_ct stable' (by simp [h0]) (by simp [h24]) (by simp [h28])
        (by simp [h32]) (by simp [h36]) (by simp) length facts.2.1 facts.1).mono
        (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ h => h)
    · intro _
      exact (ret_ct 0).mono (fun _ _ _ => trivial) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.Domain.head
  apply RelCT.assoc
  exact relCT_chain head wp wp branches

end VG.Proof.Ffdh.Arm
