module

public import VerifiedGarbage.Impl.Ffdh.Arm.VettedValidation
public import VerifiedGarbage.Proof.Ffdh.Arm.DomainBody
public import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsState
import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroups
import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsFinish
import VerifiedGarbage.Proof.Ffdh.Arm.DomainSpec
import VerifiedGarbage.Proof.Ffdh.VettedValidation.Facts
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Ffdh.Arm.Branch

/-! Exact recognition proves the existing domain-validity predicate. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.VettedValidation
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Impl.Ffdh.Arm.VettedGroups (tableSym groups recognize)

theorem body_ok (s : State) {p : Inputs} {slots : List Nat}
    (h : Context p slots s) (stable : stableSlots slots = true)
    (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots)
    (table : VettedGroups.TableAt (s.syms tableSym) groups s) :
    WP isa VG.Impl.Ffdh.Arm.VettedValidation.body s fun t =>
      t.gpr .r0 = checkedDomainFlag p ∧ Frame (bodyWrites p s) s.mem t.mem := by
  rw [VG.Impl.Ffdh.Arm.VettedValidation.body, WP.seq_iff]
  refine WP.mono (VettedGroups.code_ok s h h24 h28 h32 table) ?_
  rintro u ⟨context, cap, memU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (VettedGroups.zero_test u .r11) ?_
  rintro v ⟨⟨zero, memV⟩, restV⟩
  have value : v.z = (BitVec.ofNat 32 (recognize groups p.k p.dom) == 0) := by
    rw [zero, cap]
  by_cases hit : BitVec.ofNat 32 (recognize groups p.k p.dom) ≠ 0
  · refine WP.ite true (by simp only [eval, value, beq_eq_false_iff_ne.mpr hit]; rfl)
      (fun _ => ?_) (fun bad => Bool.noConfusion bad)
    have recognized : recognize groups p.k p.dom ≠ 0 := by
      intro impossible
      exact hit (by rw [impossible]; rfl)
    have valid := VG.Proof.Ffdh.VettedValidation.recognized_domain_valid groups
      (fun _ hg => hg) (by rw [p.domainLength]; split <;> simp) recognized
    refine WP.mono (ret_ok v 1 (by decide)) ?_
    rintro t ⟨⟨result, memT⟩, _⟩
    refine ⟨?_, ?_⟩
    · rw [checkedDomainFlag_spec, valid]
      exact result
    · rw [memT, memV, memU]
      exact Frame.refl _ _
  · have contextV := context.of_mem memV restV ((restV.gpr .r0 (by simp)).trans context.ptr)
    refine WP.ite false (by rw [Classical.not_not] at hit; simp only [eval, value, hit]; rfl)
      (fun bad => Bool.noConfusion bad) (fun _ => ?_)
    refine WP.mono (domainBody_ok v contextV stable h0 h24 h28 h32) ?_
    rintro t ⟨result, frame⟩
    refine ⟨result, ?_⟩
    rw [memV, memU] at frame
    simpa only [bodyWrites, restV.sp, restU.sp] using frame

end VG.Proof.Ffdh.Arm.VettedValidation
