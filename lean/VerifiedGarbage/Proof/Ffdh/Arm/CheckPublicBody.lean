module

public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
public import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicMain
import VerifiedGarbage.Proof.Ffdh.Arm.Head
import VerifiedGarbage.Proof.Ffdh.Arm.Branch
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
import VerifiedGarbage.Proof.Framework.Block

/-! The entire imported-public-value body, including invalid public moduli. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont

def bodyWrites (p : Inputs) (s : State) : List Region :=
  [⟨State.addr p.base, 8 * p.len⟩, ⟨State.addr s.sp, 72⟩]

def checkedPublicFlag (p : Inputs) (y : Nat) : BitVec 32 :=
  if Spec.Rsa.modulusValid p.P p.k = true then publicFlag p y else 0

theorem checkPublicBody_ok (s : State) {p : Inputs} {slots : List Nat} {yb : List Byte}
    (h : Context p slots s) (stable : stableSlots slots = true)
    (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) (h36 : 36 ∈ slots)
    (value : Octets p.base p.publicValue p.len yb s) (length : yb.length = p.k)
    (valueStack : Region.Disjoint ⟨State.addr p.publicValue, yb.length⟩ ⟨State.addr s.sp, 72⟩) :
    WP isa (VG.Impl.Ffdh.Arm.Domain.head VG.Impl.Ffdh.Arm.Domain.CheckPublic.main) s fun t =>
      t.gpr .r0 = checkedPublicFlag p (Spec.Rsa.os2ip yb) ∧ Frame (bodyWrites p s) s.mem t.mem := by
  unfold VG.Impl.Ffdh.Arm.Domain.head
  apply WP.assoc
  rw [WP.seq_iff]
  refine WP.mono (head_ok s h stable h0 h24 h32) ?_
  rintro u ⟨contextU, zero, frameU, restU⟩
  have fU : Frame (bodyWrites p s) s.mem u.mem := frameU.mono (by simp [bodyWrites])
  by_cases valid : Spec.Rsa.modulusValid p.P p.k = true
  · refine WP.ite true (by change some u.z = some true; rw [zero, valid]) ?_ (by intro hf; cases hf)
    intro _
    have facts := VG.Proof.Bignum.valid_facts valid p.minLength
    have stableU : stableSlots (60 :: 56 :: slots) = true := by
      change (true && (true && stableSlots slots)) = true
      rw [Bool.true_and, Bool.true_and, stable]
    have valueU := value.after_frame frameU restU (by
      intro r hr
      rw [List.mem_singleton] at hr
      subst r
      exact valueStack)
    have valueStackU : Region.Disjoint ⟨State.addr p.publicValue, yb.length⟩ ⟨State.addr u.sp, 72⟩ := by
      rw [restU.sp]; exact valueStack
    refine WP.mono (checkPublicMain_ok u contextU stableU
      (by simp [h0]) (by simp [h24]) (by simp [h28]) (by simp [h32]) (by simp [h36]) (by simp)
      facts.2.1 facts.1 valueU length valueStackU) ?_
    rintro t ⟨result, frameT⟩
    refine ⟨?_, fU.trans (frameT.sub ?_)⟩
    · rw [checkedPublicFlag, ite_eq_left valid]; exact result
    · intro r hr
      simp only [prepareAtWrites, prepareWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨⟨State.addr p.base, 8 * p.len⟩, by simp [bodyWrites], by intro a ha; exact ha⟩
      · refine ⟨⟨State.addr s.sp, 72⟩, by simp [bodyWrites], ?_⟩
        rw [restU.sp]
        exact Offset.sub_base _ (by decide)
      · refine ⟨⟨State.addr s.sp, 72⟩, by simp [bodyWrites], ?_⟩
        rw [restU.sp]
        exact Offset.sub_base _ (by decide)
  · have invalid : Spec.Rsa.modulusValid p.P p.k = false := Bool.eq_false_iff.mpr valid
    refine WP.ite false (by change some u.z = some false; rw [zero, invalid]) (by intro ht; cases ht) ?_
    intro _
    refine WP.mono (ret_ok u 0 (by decide)) ?_
    rintro t ⟨⟨result, memT⟩, _⟩
    refine ⟨?_, ?_⟩
    · rw [checkedPublicFlag, ite_eq_right valid]; exact result
    · rw [memT]; exact fU

end VG.Proof.Ffdh.Arm
