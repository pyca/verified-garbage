module

public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Ffdh.Arm.SubgroupCT

import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicMain
import VerifiedGarbage.Proof.Ffdh.Arm.PrepareAtCT
import VerifiedGarbage.Proof.Ffdh.Arm.ImportAtCT
import VerifiedGarbage.Proof.Ffdh.Arm.Range
import VerifiedGarbage.Proof.Ffdh.Arm.RangeCT
import VerifiedGarbage.Proof.Ffdh.Arm.BranchCT
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ffdh.Arm.Branch
import VerifiedGarbage.Proof.Ffdh.Arm.ImportAt
import VerifiedGarbage.Proof.Ffdh.Arm.QTest
/-! The imported public value controls only the documented public validation branches. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/CheckPublicTailCT.lean`, which only this module imported.
section

/-! Optional public subgroup checking branches only on the public domain shape. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem checkPublicTail_ct {p : Inputs} {slots : List Nat} {yb : List Byte}
    (stable : stableSlots slots = true) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots)
    (h36 : 36 ∈ slots) (h60 : 60 ∈ slots) (length : yb.length = p.k) (odd : p.P % 2 = 1) :
    RelCT isa (fun s t => SubgroupInput p slots 36 yb s ∧ SubgroupInput p slots 36 yb t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.Domain.withQ
        (.seq (VG.Impl.Ffdh.Arm.Domain.subgroup 36) VG.Impl.Ffdh.Arm.Domain.finishFlag)
        (VG.Impl.Ffdh.Arm.Domain.ret 1)) (fun _ _ => True) := by
  let P := SubgroupInput p slots 36 yb
  let Q := fun s : State => P s ∧ s.z = !p.hasQ
  have trace := qTest_ct.mono (P' := fun (s t : State) => P s ∧ P t ∧ s.sp = t.sp)
    (fun _ _ h => h.2.2) (fun _ _ _ => trivial)
  have wp (s : State) (h : P s) : WP isa VG.Impl.Ffdh.Arm.Domain.qTest s Q := by
    refine WP.mono (qTest_ok s h.context h28 h32) ?_
    rintro u ⟨⟨zero, mem⟩, rest⟩
    exact ⟨h.after_mem stable mem rest ((rest.gpr .r0 (by simp)).trans h.context.ptr), zero⟩
  have branches : RelCT isa (fun s t => Q s ∧ Q t ∧ s.sp = t.sp)
      (.ite .ne (.seq (VG.Impl.Ffdh.Arm.Domain.subgroup 36) VG.Impl.Ffdh.Arm.Domain.finishFlag)
        (VG.Impl.Ffdh.Arm.Domain.ret 1)) (fun _ _ => True) := by
    apply iteKnown_ct p.hasQ (fun s h => by simp only [eval, h.2, Bool.not_not])
    · intro hasQ
      exact ((subgroup_ct stable h36 h60 h32 hasQ length odd).seq finishFlag_ct).mono
        (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ h => h)
    · intro _
      exact (ret_ct 1).mono (fun _ _ _ => trivial) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.Domain.withQ
  exact relCT_chain trace wp wp branches

end VG.Proof.Ffdh.Arm
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt Operand arrAt)

structure PublicMainInput (p : Inputs) (slots : List Nat) (yb : List Byte) (s : State) : Prop where
  context : Context p slots s
  value : Octets p.base p.publicValue p.len yb s
  separate : Region.Disjoint ⟨State.addr p.publicValue, yb.length⟩ ⟨State.addr s.sp, 72⟩

structure PublicImported (p : Inputs) (slots : List Nat) (yb : List Byte) (s : State) : Prop extends
    SubgroupInput p slots 36 yb s where
  value : numAt s.mem (State.addr p.base) p.w 1 = Spec.Rsa.os2ip yb

structure PublicRanged (p : Inputs) (slots : List Nat) (yb : List Byte) (s : State) : Prop extends
    SubgroupInput p slots 36 yb s where
  flag : s.gpr .r11 = if 1 < Spec.Rsa.os2ip yb ∧ Spec.Rsa.os2ip yb < p.P - 1 then 1 else 0

theorem checkPublicMain_ct {p : Inputs} {slots : List Nat} {yb : List Byte}
    (stable : stableSlots slots = true) (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots)
    (h32 : 32 ∈ slots) (h36 : 36 ∈ slots) (h60 : 60 ∈ slots)
    (length : yb.length = p.k) (large : 1 < p.P) (odd : p.P % 2 = 1) :
    RelCT isa (fun s t => PublicMainInput p slots yb s ∧ PublicMainInput p slots yb t ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.Domain.CheckPublic.main (fun _ _ => True) := by
  have op0 : Operand 0 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op1 : Operand 1 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have pStack (s : State) (h : PublicMainInput p slots yb s) :
      Region.Disjoint ⟨State.addr p.domain, p.k⟩ ⟨State.addr s.sp, 72⟩ :=
    h.context.domainStack.sub_left (Region.sub_prefix (by rw [p.domainLength]; split <;> omega))
  have prep := (prepareAt_ct (p := p) (slot := 24) stable h24 h32 h0 p.pLength large odd).mono
    (P' := fun (s t : State) => PublicMainInput p slots yb s ∧ PublicMainInput p slots yb t ∧ s.sp = t.sp)
    (fun s t h => ⟨⟨h.1.context, h.1.context.pBytes, pStack s h.1⟩,
      ⟨h.2.1.context, h.2.1.context.pBytes, pStack t h.2.1⟩, h.2.2⟩) (fun _ _ h => h)
  have wpPrep (s : State) (h : PublicMainInput p slots yb s) :
      WP isa (VG.Impl.Ffdh.Arm.Domain.prepareAt 24) s (SubgroupInput p slots 36 yb) := by
    refine WP.mono (prepareAt_ok s 24 h.context stable h24 h32 h0 h.context.pBytes p.pLength (pStack s h) large odd) ?_
    rintro u ⟨context, ready, modulus, r2, frame, rest⟩
    exact ⟨context, ready, modulus, r2, h.value.after_frame frame rest (by
      intro r hr
      simp only [prepareAtWrites, prepareWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h.value.separate
      · exact h.separate.sub_right (Offset.sub_base _ (by decide))
      · exact h.separate.sub_right (Offset.sub_base _ (by decide)))⟩
  have imports := (importAt_ct (p := p) (a := 1) stable h36 h32
    (show p.slotValue 32 = BitVec.ofNat 32 yb.length by change BitVec.ofNat 32 p.k = _; rw [length]) (by decide)).mono
    (P' := fun (s t : State) => SubgroupInput p slots 36 yb s ∧ SubgroupInput p slots 36 yb t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨⟨h.1.context, h.1.ready⟩, ⟨h.2.1.context, h.2.1.ready⟩, h.2.2⟩) (fun _ _ h => h)
  have wpImport (s : State) (h : SubgroupInput p slots 36 yb s) :
      WP isa (VG.Impl.Ffdh.Arm.Domain.importAt 1 36 32) s (PublicImported p slots yb) := by
    refine WP.mono (importAt_ok s 1 36 32 h.context stable h36 h32 h.ready (by decide) (by decide) h.source
      (by rw [length]; have := p.minLength; omega) (by rw [length]; exact p.width.2.2.2.1)
      (by change BitVec.ofNat 32 p.k = _; rw [length])) ?_
    rintro u ⟨context, ready, value, keeps, frame, rest⟩
    have fits : arrAt p.w 8 ≤ 8 * p.len := ready.width ▸ ready.layout.2.2.1
    exact ⟨⟨context, ready, (keeps_array_num keeps fits op0 (by decide)).trans h.modulus,
      (keeps_array_num keeps fits op4 (by decide)).trans h.r2, h.source.after_workspace frame rest⟩, value⟩
  have range := (inRange_ct (base := p.base) (len := p.len) (w := p.w) op1 (by decide)).mono
    (P' := fun (s t : State) => PublicImported p slots yb s ∧ PublicImported p slots yb t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.ready, h.2.1.ready, h.2.2⟩) (fun _ _ h => h)
  have wpRange (s : State) (h : PublicImported p slots yb s) :
      WP isa (VG.Impl.Ffdh.Arm.inRange 1) s (PublicRanged p slots yb) := by
    refine WP.mono (inRange_ok s h.ready op1 (by decide) (by rw [h.modulus]; exact odd)) ?_
    rintro u ⟨ready, flag, arrays, frame, rest⟩
    rw [h.value, h.modulus] at flag
    exact ⟨h.toSubgroupInput.after_workspace stable frame rest ready
      ((arrays 0 op0 (by decide)).trans h.modulus) ((arrays 4 op4 (by decide)).trans h.r2), flag⟩
  let valid : Prop := 1 < Spec.Rsa.os2ip yb ∧ Spec.Rsa.os2ip yb < p.P - 1
  let Q := fun s : State => SubgroupInput p slots 36 yb s ∧ s.z = !decide valid
  have tests := testFlag_ct.mono
    (P' := fun (s t : State) => PublicRanged p slots yb s ∧ PublicRanged p slots yb t ∧ s.sp = t.sp)
    (fun _ _ _ => trivial) (fun _ _ h => h)
  have wpTest (s : State) (h : PublicRanged p slots yb s) :
      WP isa VG.Impl.Ffdh.Arm.Domain.testFlag s Q := by
    refine WP.mono (testFlag_ok s) ?_
    rintro u ⟨⟨zero, mem⟩, rest⟩
    refine ⟨h.toSubgroupInput.after_mem stable mem rest ((rest.gpr .r0 (by simp)).trans h.context.ptr), ?_⟩
    rw [zero, h.flag]
    change ((if valid then (1#32) else 0#32) == 0#32) = !decide valid
    by_cases hv : valid
    · rw [ite_eq_left hv, decide_eq_true hv]; rfl
    · rw [ite_eq_right hv, decide_eq_false hv]; rfl
  have branches : RelCT isa (fun s t => Q s ∧ Q t ∧ s.sp = t.sp)
      (.ite .ne (VG.Impl.Ffdh.Arm.Domain.withQ
        (.seq (VG.Impl.Ffdh.Arm.Domain.subgroup 36) VG.Impl.Ffdh.Arm.Domain.finishFlag)
        (VG.Impl.Ffdh.Arm.Domain.ret 1)) (VG.Impl.Ffdh.Arm.Domain.ret 0)) (fun _ _ => True) := by
    apply iteKnown_ct (decide valid) (fun s h => by simp only [eval, h.2, Bool.not_not])
    · intro _
      exact (checkPublicTail_ct stable h28 h32 h36 h60 length odd).mono
        (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ h => h)
    · intro _
      exact (ret_ct 0).mono (fun _ _ _ => trivial) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.Domain.CheckPublic.main VG.Impl.Ffdh.Arm.Domain.ifFlag
  exact relCT_chain prep wpPrep wpPrep (relCT_chain imports wpImport wpImport
    (relCT_chain range wpRange wpRange (relCT_chain tests wpTest wpTest branches)))

end VG.Proof.Ffdh.Arm
