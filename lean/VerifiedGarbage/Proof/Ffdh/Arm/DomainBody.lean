module

public import VerifiedGarbage.Proof.Ffdh.Arm.DomainMain
import VerifiedGarbage.Proof.Ffdh.Arm.Head
public import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicBody
import VerifiedGarbage.Proof.Ffdh.Arm.Branch
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
import VerifiedGarbage.Proof.Framework.Block

/-! Full native parameter validation, including a rejected modulus shape. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont

def checkedDomainFlag (p : Inputs) : BitVec 32 :=
  if Spec.Rsa.modulusValid p.P p.k = true then domainMainFlag p p.G else 0

theorem domainBody_ok (s : State) {p : Inputs} {slots : List Nat}
    (h : Context p slots s) (stable : stableSlots slots = true)
    (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) :
    WP isa (VG.Impl.Ffdh.Arm.Domain.head VG.Impl.Ffdh.Arm.Domain.CheckDomain.main) s fun t =>
      t.gpr .r0 = checkedDomainFlag p ∧ Frame (bodyWrites p s) s.mem t.mem := by
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
    have gStack : Region.Disjoint ⟨State.addr p.g, ((p.dom.drop p.k).take p.k).length⟩ ⟨State.addr u.sp, 72⟩ := by
      rw [p.gLength]
      exact contextU.toArgumentMemory.domainSliceStack (by have := p.minLength; omega)
        (by rw [p.domainLength]; split <;> omega)
    refine WP.mono (domainMain_ok u contextU stableU (by simp [h0]) (by simp [h24]) (by simp [h28])
      (by simp [h32]) (by simp) (by simp) facts.2.1 facts.1 contextU.gBytes p.gLength gStack) ?_
    rintro t ⟨result, frameT⟩
    refine ⟨by rw [checkedDomainFlag, ite_eq_left valid]; exact result, fU.trans (frameT.sub ?_)⟩
    intro r hr
    simp only [prepareAtWrites, prepareWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨State.addr p.base, 8 * p.len⟩, by simp [bodyWrites], by intro a ha; exact ha⟩
    · refine ⟨⟨State.addr s.sp, 72⟩, by simp [bodyWrites], ?_⟩
      rw [restU.sp]; exact Offset.sub_base _ (by decide)
    · refine ⟨⟨State.addr s.sp, 72⟩, by simp [bodyWrites], ?_⟩
      rw [restU.sp]; exact Offset.sub_base _ (by decide)
  · have invalid : Spec.Rsa.modulusValid p.P p.k = false := Bool.eq_false_iff.mpr valid
    refine WP.ite false (by change some u.z = some false; rw [zero, invalid]) (by intro ht; cases ht) ?_
    intro _
    refine WP.mono (ret_ok u 0 (by decide)) ?_
    rintro t ⟨⟨result, memT⟩, _⟩
    exact ⟨by rw [checkedDomainFlag, ite_eq_right valid]; exact result, by rw [memT]; exact fU⟩

end VG.Proof.Ffdh.Arm
