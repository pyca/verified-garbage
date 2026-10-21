module

public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicTail
public import VerifiedGarbage.Proof.Ffdh.Arm.SharedCheckPublicStateCT
public import VerifiedGarbage.Impl.Ffdh.Arm.SharedCheckPublic
import VerifiedGarbage.Proof.Ffdh.Arm.SharedCheckPublicSubgroupCT
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
import VerifiedGarbage.Proof.Ffdh.Arm.BranchCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.QTest
public import VerifiedGarbage.Proof.Ffdh.Arm.Context

/-! Optional public subgroup checking branches only on the public domain shape. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem sharedCheckPublicTail_ct (backend : MontBackend) {p : Inputs} {slots : List Nat} {yb : List Byte}
    (stable : stableSlots slots = true) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots)
    (h36 : 36 ∈ slots) (h60 : 60 ∈ slots) (length : yb.length = p.k) (odd : p.P % 2 = 1) :
    RelCT isa (fun s t => SharedSubgroupInput p slots 36 yb s ∧ SharedSubgroupInput p slots 36 yb t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.Domain.withQ
        (.seq (VG.Impl.Ffdh.Arm.SharedCheckPublic.subgroup
          (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) 36) VG.Impl.Ffdh.Arm.Domain.finishFlag)
        (VG.Impl.Ffdh.Arm.Domain.ret 1)) (fun _ _ => True) := by
  let P := SharedSubgroupInput p slots 36 yb
  let Q := fun s : State => P s ∧ s.z = !p.hasQ
  have trace := qTest_ct.mono (P' := fun (s t : State) => P s ∧ P t ∧ s.sp = t.sp)
    (fun _ _ h => h.2.2) (fun _ _ _ => trivial)
  have wp (s : State) (h : P s) : WP isa VG.Impl.Ffdh.Arm.Domain.qTest s Q := by
    refine WP.mono (qTest_ok s h.context h28 h32) ?_
    rintro u ⟨⟨zero, mem⟩, rest⟩
    exact ⟨⟨h.toSubgroupInput.after_mem stable mem rest ((rest.gpr .r0 (by simp)).trans h.context.ptr), h.calls.after rest⟩, zero⟩
  have branches : RelCT isa (fun s t => Q s ∧ Q t ∧ s.sp = t.sp)
      (.ite .ne (.seq (VG.Impl.Ffdh.Arm.SharedCheckPublic.subgroup
          (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) 36) VG.Impl.Ffdh.Arm.Domain.finishFlag)
        (VG.Impl.Ffdh.Arm.Domain.ret 1)) (fun _ _ => True) := by
    apply iteKnown_ct p.hasQ (fun s h => by simp only [eval, h.2, Bool.not_not])
    · intro hasQ
      exact ((sharedCheckPublicSubgroup_ct backend stable h36 h60 h32 hasQ length odd).seq finishFlag_ct).mono
        (fun _ _ h => ⟨⟨h.1.1.toSubgroupInput,h.1.1.calls⟩, ⟨h.2.1.1.toSubgroupInput,h.2.1.1.calls⟩, h.2.2⟩) (fun _ _ h => h)
    · intro _
      exact (ret_ct 1).mono (fun _ _ _ => trivial) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.Domain.withQ
  exact relCT_chain trace wp wp branches

end VG.Proof.Ffdh.Arm
