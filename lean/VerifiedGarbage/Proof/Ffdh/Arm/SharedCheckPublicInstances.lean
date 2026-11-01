module

public import VerifiedGarbage.Proof.Ffdh.Arm.SharedCheckPublicPrograms
public import VerifiedGarbage.Spec.Ffdh.Contract

import VerifiedGarbage.Proof.Ffdh.Arm.SubgroupCT
import VerifiedGarbage.Proof.Ffdh.Arm.DomainCallMemory
import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
import VerifiedGarbage.Impl.Ffdh.Arm.SharedCheckPublic
import VerifiedGarbage.Proof.Ffdh.Arm.SharedCheckPublicPublicPowerCT
import VerifiedGarbage.Proof.Ffdh.Arm.SharedCheckPublicPublicPower
import VerifiedGarbage.Proof.Ffdh.Arm.ValueChecksCT
import VerifiedGarbage.Proof.Bignum.Arm.TwoExpSharedCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Impl.Ffdh.Arm.Domain
import VerifiedGarbage.Proof.Ffdh.Arm.SharedCheckPublicStateCT
import VerifiedGarbage.Proof.Ffdh.Arm.BranchCT
import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.QTest
import VerifiedGarbage.Proof.Ffdh.Arm.Context
import VerifiedGarbage.Impl.Ffdh.Arm.SharedPrepare
import VerifiedGarbage.Proof.Ffdh.Arm.DomainSharedPrepareAt
import VerifiedGarbage.Proof.Ffdh.Arm.SharedPrepareCT
import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
import VerifiedGarbage.Impl.Bignum.Arm.MontCall
import VerifiedGarbage.Proof.Ffdh.Arm.ImportAtCT
import VerifiedGarbage.Proof.Ffdh.Arm.Range
import VerifiedGarbage.Proof.Ffdh.Arm.RangeCT
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ffdh.Arm.Branch
import VerifiedGarbage.Proof.Ffdh.Arm.ImportAt
import VerifiedGarbage.TCB.Arm.Isa
import VerifiedGarbage.Proof.Ffdh.Arm.Head
import VerifiedGarbage.Proof.Ffdh.Arm.HeadCT
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Ffdh.Arm.SharedCheckPublicFn
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicEntryCT
import VerifiedGarbage.Proof.Ffdh.Arm.FrameCT
import VerifiedGarbage.Proof.Ffdh.Arm.Entered
import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicEntry
import VerifiedGarbage.Proof.Ffdh.Arm.SharedCheckPublicCorrect
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Sig
import Init.Data.BitVec.Basic
import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Ffdh.Arm.SharedCheckPublicPre
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import Batteries.Logic
/-! The backend's caller transformation preserves shared Montgomery calls. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/SharedCheckPublicSubgroupCT.lean`, which only this module imported.
section

/-! Public subgroup checking calls the shared Montgomery window. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (Operand)

theorem sharedCheckPublicSubgroup_ct (backend : MontBackend) {p : Inputs} {slots : List Nat}
    {slot : Nat} {bb : List Byte} (stable : stableSlots slots = true)
    (hb : slot ∈ slots) (h60 : 60 ∈ slots) (h32 : 32 ∈ slots)
    (hasQ : p.hasQ = true) (baseLength : bb.length = p.k) (odd : p.P % 2 = 1) :
    RelCT isa (fun s t => (SubgroupInput p slots slot bb s ∧ DomainCallMemory p s) ∧
      (SubgroupInput p slots slot bb t ∧ DomainCallMemory p t) ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.SharedCheckPublic.subgroup
        (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) slot) (fun _ _ => True) := by
  have positive : 0 < ((p.dom.drop (2*p.k)).take p.k).length := by
    rw [p.qLength hasQ]; have := p.minLength; omega
  have fits : ((p.dom.drop (2*p.k)).take p.k).length < 2^32 := by
    rw [p.qLength hasQ]; have := p.maxLength; omega
  have count : p.slotValue 32 = BitVec.ofNat 32 ((p.dom.drop (2*p.k)).take p.k).length := by
    change BitVec.ofNat 32 p.k = _; rw [p.qLength hasQ]
  have family (sp0 : BitVec 32) :
      RelCT isa (fun s t => (SubgroupInput p slots slot bb s ∧ DomainCallMemory p s ∧ s.sp = sp0) ∧
        (SubgroupInput p slots slot bb t ∧ DomainCallMemory p t ∧ t.sp = sp0) ∧ s.sp = t.sp)
        (VG.Impl.Ffdh.Arm.SharedCheckPublic.subgroup
          (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) slot) (fun _ _ => True) := by
    intro s t tr1 tr2 u v initial run1 run2
    let correct := fun o a b ho ha hb v input => backend.correct v (base := p.base) (len := p.len)
      (w := p.w) (o := o) (a := a) (b := b) input ho ha hb
    let K := TwoExp.sharedMontgomery p.base sp0 p.len p.w backend.name backend.mul correct backend.stackOk
    have timing : TwoExp.MontgomeryTiming K :=
      TwoExp.sharedMontgomeryTiming p.base sp0 p.len p.w backend.name backend.mul correct backend.stackOk
        (fun _ _ _ ho ha hb => backend.rawCT ho ha hb)
    have below (s : State) (h : SubgroupInput p slots slot bb s ∧ DomainCallMemory p s ∧ s.sp = sp0) :
        Region.Disjoint ⟨State.addr (p.slotValue 60), ((p.dom.drop (2*p.k)).take p.k).length⟩
          (FrameStack.belowA sp0 48) := by
      change Region.Disjoint ⟨State.addr p.q, _⟩ _
      rw [p.qLength hasQ, ←h.2.2]
      exact h.2.1.domainSlice h.1.context (by have := p.minLength; omega)
        (by rw [p.domainLength,hasQ]; simp only [ite_true]; omega)
    have separate : ∀ r ∈ [⟨State.addr p.base,8*p.len⟩,FrameStack.belowA sp0 48],
        Region.Disjoint ⟨State.addr (p.slotValue 60), ((p.dom.drop (2*p.k)).take p.k).length⟩ r := by
      intro r hr
      rcases List.mem_cons.mp hr with hr | hr
      · subst r
        exact (initial.1.1.context.qBytes hasQ).separate
      · have eq := List.mem_singleton.mp hr; subst r
        exact below s initial.1
    have powers := sharedCheckPublicPublicPower_ct K timing stable hb h60 h32 h32
      baseLength positive fits count odd separate
    have wp (s : State) (h : SubgroupInput p slots slot bb s ∧ DomainCallMemory p s ∧ s.sp = sp0) :=
      WP.mono (sharedCheckPublicPublicPower_ok backend s slot 60 32 h.1.context h.2.1 stable hb h60 h32 h32
        h.1.ready h.1.modulus odd h.1.r2 h.1.source baseLength (h.1.context.qBytes hasQ)
        positive fits count (by rw [h.2.2]; exact below s h)) fun _ j => j.2.1
    exact (relCT_chain (powers.mono (fun _ _ h =>
      ⟨⟨⟨h.1.1.context,h.1.1.ready,h.1.1.modulus,h.1.1.r2,h.1.1.source,h.1.1.context.qBytes hasQ⟩,
          h.1.2.1.stack,h.1.2.2⟩,
        ⟨⟨h.2.1.1.context,h.2.1.1.ready,h.2.1.1.modulus,h.2.1.1.r2,h.2.1.1.source,h.2.1.1.context.qBytes hasQ⟩,
          h.2.1.2.1.stack,h.2.1.2.2⟩,h.2.2⟩) (fun _ _ h => h)) wp wp
      (isOne_ct (by simp [Operand,Proof.Rsa.Mont.aAcc,Proof.Rsa.Mont.aTmp] : Operand 6)))
      s t tr1 tr2 u v initial run1 run2
  intro s t tr1 tr2 u v h e1 e2
  exact family s.sp s t tr1 tr2 u v
    ⟨⟨h.1.1,h.1.2,rfl⟩,⟨h.2.1.1,h.2.1.2,h.2.2.symm⟩,h.2.2⟩ e1 e2

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/SharedCheckPublicTailCT.lean`, which only this module imported.
section

/-! Optional public subgroup checking branches only on the public domain shape. -/

section
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
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/DomainSharedPrepareAtCT.lean`, which only this module imported.
section

/-! # The shared native domain-preparation boundary hides modulus values -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem domainSharedPrepareAt24_ct (backend : MontBackend) {p : Inputs} {slots : List Nat}
    (stable : stableSlots slots = true) (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h32 : 32 ∈ slots)
    (large : 1 < p.P) (odd : p.P % 2 = 1) :
    RelCT isa (fun s t => (Context p slots s ∧ DomainCallMemory p s) ∧
      (Context p slots t ∧ DomainCallMemory p t) ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.SharedPrepare.prepareAt
        (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) 24) (fun _ _ => True) := by
  have family (sp0 : BitVec 32) :
      RelCT isa (fun s t => (Context p slots s ∧ DomainCallMemory p s ∧ s.sp = sp0) ∧
        (Context p slots t ∧ DomainCallMemory p t ∧ t.sp = sp0) ∧ s.sp = t.sp)
        (VG.Impl.Ffdh.Arm.SharedPrepare.prepareAt
          (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) 24) (fun _ _ => True) := by
    let correct := fun o a b ho ha hb v input => backend.correct v (base := p.base) (len := p.len) (w := p.w) (o := o) (a := a) (b := b) input ho ha hb
    let K := TwoExp.sharedMontgomery p.base sp0 p.len p.w backend.name backend.mul correct backend.stackOk
    have timing : TwoExp.MontgomeryTiming K :=
      TwoExp.sharedMontgomeryTiming p.base sp0 p.len p.w backend.name backend.mul correct backend.stackOk
        (fun _ _ _ ho ha hb => backend.rawCT ho ha hb)
    have argsInput (s : State) (h : Context p slots s ∧ DomainCallMemory p s ∧ s.sp = sp0) :
        WP isa (.block (VG.Impl.Ffdh.Arm.Domain.prepareArgs 24)) s fun u =>
          PrepareInput p.base p.domain p.len p.k u ∧ TwoExp.CallReady p.base sp0 p.len u := by
      refine WP.mono (prepareArgs_ok s 24 h.1 stable h24 h32 h0) ?_
      rintro u ⟨contextU, stack, _, countU, _, _, restU⟩
      have sourceU := contextU.pBytes
      have bytes : Spec.Rsa.bytesAt u.mem (State.addr p.domain) p.k = p.dom.take p.k := by
        simpa only [p.pLength] using sourceU.bytes
      refine ⟨?_, (h.2.1.after restU).stack, restU.sp.trans h.2.2⟩
      exact ⟨contextU.workspace, by rw [stack.savedOutput]; exact stack, contextU.ptr, countU,
        p.minLength, p.maxLength, p.publicSpace,
        by rw [← p.pLength]; exact sourceU.fits,
        by rw [← p.pLength]; exact sourceU.readable,
        by rw [← p.pLength]; exact sourceU.separate,
        by rw [bytes]; exact large, by rw [bytes]; exact odd⟩
    unfold VG.Impl.Ffdh.Arm.SharedPrepare.prepareAt
    exact relCT_chain ((prepareArgs_ct 24).mono (fun _ _ h => h.2.2) (fun _ _ h => h))
      argsInput argsInput (sharedPrepare_ct K timing p.width.2.2.2.2)
  intro s t tr1 tr2 u v h e1 e2
  exact family s.sp s t tr1 tr2 u v
    ⟨⟨h.1.1, h.1.2, rfl⟩, ⟨h.2.1.1, h.2.1.2, h.2.2.symm⟩, h.2.2⟩ e1 e2


end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/SharedCheckPublicMainCT.lean`, which only this module imported.
section

/-! The imported public value controls only the documented public validation branches. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt Operand arrAt)

theorem sharedCheckPublicMain_ct (backend : MontBackend) {p : Inputs} {slots : List Nat} {yb : List Byte}
    (stable : stableSlots slots = true) (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots)
    (h32 : 32 ∈ slots) (h36 : 36 ∈ slots) (h60 : 60 ∈ slots)
    (length : yb.length = p.k) (large : 1 < p.P) (odd : p.P % 2 = 1) :
    RelCT isa (fun s t => SharedPublicMainInput p slots yb s ∧ SharedPublicMainInput p slots yb t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.SharedCheckPublic.main (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) (fun _ _ => True) := by
  have op0 : Operand 0 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op1 : Operand 1 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have prep := (domainSharedPrepareAt24_ct backend stable h0 h24 h32 large odd).mono
    (P' := fun (s t : State) => SharedPublicMainInput p slots yb s ∧ SharedPublicMainInput p slots yb t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨⟨h.1.context,h.1.calls⟩,⟨h.2.1.context,h.2.1.calls⟩,h.2.2⟩) (fun _ _ h => h)
  have wpPrep (s : State) (h : SharedPublicMainInput p slots yb s) :
      WP isa (VG.Impl.Ffdh.Arm.SharedPrepare.prepareAt (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) 24) s (SharedSubgroupInput p slots 36 yb) := by
    refine WP.mono (domainSharedPrepareAt24_ok backend s h.context h.calls stable h0 h24 h32 large odd) ?_
    rintro u ⟨context, ready, modulus, r2, frame, rest⟩
    refine ⟨⟨context, ready, modulus, r2, h.value.after_frame frame rest ?_⟩, h.calls.after rest⟩
    intro r hr
    simp only [domainPrepareWrites, List.mem_append, List.mem_singleton] at hr
    rcases hr with hr | rfl
    · simp only [prepareAtWrites, prepareWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h.value.separate
      · exact h.separate.sub_right (Offset.sub_base _ (by decide))
      · exact h.separate.sub_right (Offset.sub_base _ (by decide))
    · rw [length]
      exact h.calls.publicValue
  have imports := (importAt_ct (p := p) (a := 1) stable h36 h32
    (show p.slotValue 32 = BitVec.ofNat 32 yb.length by change BitVec.ofNat 32 p.k = _; rw [length]) (by decide)).mono
    (P' := fun (s t : State) => SharedSubgroupInput p slots 36 yb s ∧ SharedSubgroupInput p slots 36 yb t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨⟨h.1.context, h.1.ready⟩, ⟨h.2.1.context, h.2.1.ready⟩, h.2.2⟩) (fun _ _ h => h)
  have wpImport (s : State) (h : SharedSubgroupInput p slots 36 yb s) :
      WP isa (VG.Impl.Ffdh.Arm.Domain.importAt 1 36 32) s (SharedPublicImported p slots yb) := by
    refine WP.mono (importAt_ok s 1 36 32 h.context stable h36 h32 h.ready (by decide) (by decide) h.source
      (by rw [length]; have := p.minLength; omega) (by rw [length]; exact p.width.2.2.2.1)
      (by change BitVec.ofNat 32 p.k = _; rw [length])) ?_
    rintro u ⟨context, ready, value, keeps, frame, rest⟩
    have fits : arrAt p.w 8 ≤ 8 * p.len := ready.width ▸ ready.layout.2.2.1
    exact ⟨⟨⟨context, ready, (keeps_array_num keeps fits op0 (by decide)).trans h.modulus,
      (keeps_array_num keeps fits op4 (by decide)).trans h.r2, h.source.after_workspace frame rest⟩, value⟩,
      h.calls.after rest⟩
  have range := (inRange_ct (base := p.base) (len := p.len) (w := p.w) op1 (by decide)).mono
    (P' := fun (s t : State) => SharedPublicImported p slots yb s ∧ SharedPublicImported p slots yb t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.ready, h.2.1.ready, h.2.2⟩) (fun _ _ h => h)
  have wpRange (s : State) (h : SharedPublicImported p slots yb s) :
      WP isa (VG.Impl.Ffdh.Arm.inRange 1) s (SharedPublicRanged p slots yb) := by
    refine WP.mono (inRange_ok s h.ready op1 (by decide) (by rw [h.modulus]; exact odd)) ?_
    rintro u ⟨ready, flag, arrays, frame, rest⟩
    rw [h.value, h.modulus] at flag
    exact ⟨⟨h.toPublicImported.toSubgroupInput.after_workspace stable frame rest ready
      ((arrays 0 op0 (by decide)).trans h.modulus) ((arrays 4 op4 (by decide)).trans h.r2), flag⟩,
      h.calls.after rest⟩
  let valid : Prop := 1 < Spec.Rsa.os2ip yb ∧ Spec.Rsa.os2ip yb < p.P - 1
  let Q := fun s : State => SharedSubgroupInput p slots 36 yb s ∧ s.z = !decide valid
  have tests := testFlag_ct.mono
    (P' := fun (s t : State) => SharedPublicRanged p slots yb s ∧ SharedPublicRanged p slots yb t ∧ s.sp = t.sp)
    (fun _ _ _ => trivial) (fun _ _ h => h)
  have wpTest (s : State) (h : SharedPublicRanged p slots yb s) :
      WP isa VG.Impl.Ffdh.Arm.Domain.testFlag s Q := by
    refine WP.mono (testFlag_ok s) ?_
    rintro u ⟨⟨zero, mem⟩, rest⟩
    refine ⟨⟨h.toPublicRanged.toSubgroupInput.after_mem stable mem rest ((rest.gpr .r0 (by simp)).trans h.context.ptr), h.calls.after rest⟩, ?_⟩
    rw [zero, h.flag]
    change ((if valid then (1#32) else 0#32) == 0#32) = !decide valid
    by_cases hv : valid
    · rw [ite_eq_left hv, decide_eq_true hv]; rfl
    · rw [ite_eq_right hv, decide_eq_false hv]; rfl
  have branches : RelCT isa (fun s t => Q s ∧ Q t ∧ s.sp = t.sp)
      (.ite .ne (VG.Impl.Ffdh.Arm.Domain.withQ
        (.seq (VG.Impl.Ffdh.Arm.SharedCheckPublic.subgroup (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) 36) VG.Impl.Ffdh.Arm.Domain.finishFlag)
        (VG.Impl.Ffdh.Arm.Domain.ret 1)) (VG.Impl.Ffdh.Arm.Domain.ret 0)) (fun _ _ => True) := by
    apply iteKnown_ct (decide valid) (fun s h => by simp only [eval, h.2, Bool.not_not])
    · intro _
      exact (sharedCheckPublicTail_ct backend stable h28 h32 h36 h60 length odd).mono
        (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ h => h)
    · intro _
      exact (ret_ct 0).mono (fun _ _ _ => trivial) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.SharedCheckPublic.main VG.Impl.Ffdh.Arm.SharedCheckPublic.tail VG.Impl.Ffdh.Arm.Domain.ifFlag
  exact relCT_chain prep wpPrep wpPrep (relCT_chain imports wpImport wpImport
    (relCT_chain range wpRange wpRange (relCT_chain tests wpTest wpTest branches)))

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/SharedCheckPublicBodyCT.lean`, which only this module imported.
section

/-! The public-value body has a trace determined by its documented public inputs. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem sharedCheckPublicBody_ct (backend : MontBackend) {p : Inputs} {slots : List Nat} {yb : List Byte}
    (stable : stableSlots slots = true) (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots)
    (h32 : 32 ∈ slots) (h36 : 36 ∈ slots) (length : yb.length = p.k) :
    RelCT isa (fun s t => SharedPublicMainInput p slots yb s ∧ SharedPublicMainInput p slots yb t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.Domain.head (VG.Impl.Ffdh.Arm.SharedCheckPublic.main (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul))) (fun _ _ => True) := by
  let Q := fun s : State => SharedPublicMainInput p (60 :: 56 :: slots) yb s ∧ s.z = Spec.Rsa.modulusValid p.P p.k
  have head := (head_ct stable h0 h24 h32).mono
    (P' := fun (s t : State) => SharedPublicMainInput p slots yb s ∧ SharedPublicMainInput p slots yb t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.context, h.2.1.context, h.2.2⟩) (fun _ _ h => h)
  have wp (s : State) (h : SharedPublicMainInput p slots yb s) :
      WP isa (.seq (.block (VG.Impl.Ffdh.Arm.Domain.prepareArgs 24 ++ VG.Impl.Ffdh.Arm.Domain.domainPointers))
        (.block VG.Impl.Bignum.Arm.modulusCheck)) s Q := by
    refine WP.mono (head_ok s h.context stable h0 h24 h32) ?_
    rintro u ⟨context, zero, frame, rest⟩
    refine ⟨⟨⟨context, h.value.after_frame frame rest (by
      intro r hr
      rw [List.mem_singleton] at hr
      subst r
      exact h.separate), ?_⟩, ?_⟩, zero⟩
    · rw [rest.sp]; exact h.separate
    · exact h.calls.after rest
  have stable' : stableSlots (60 :: 56 :: slots) = true := by
    change (true && (true && stableSlots slots)) = true
    rw [Bool.true_and, Bool.true_and, stable]
  have branches : RelCT isa (fun s t => Q s ∧ Q t ∧ s.sp = t.sp)
      (.ite .eq (VG.Impl.Ffdh.Arm.SharedCheckPublic.main (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) (VG.Impl.Ffdh.Arm.Domain.ret 0)) (fun _ _ => True) := by
    apply iteKnown_ct (Spec.Rsa.modulusValid p.P p.k) (fun s h => by change some s.z = _; rw [h.2])
    · intro valid
      have facts := VG.Proof.Bignum.valid_facts valid p.minLength
      exact (sharedCheckPublicMain_ct backend stable' (by simp [h0]) (by simp [h24]) (by simp [h28])
        (by simp [h32]) (by simp [h36]) (by simp) length facts.2.1 facts.1).mono
        (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ h => h)
    · intro _
      exact (ret_ct 0).mono (fun _ _ _ => trivial) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.Domain.head
  apply RelCT.assoc
  exact relCT_chain head wp wp branches

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/SharedCheckPublicFnCT.lean`, which only this module imported.
section

/-! The complete callable public check reveals only public FFDH inputs. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem sharedCheckPublicFn_ct (backend : MontBackend) {p : Inputs} {yb : List Byte} (length : yb.length = p.k) :
    RelCT isa (fun s t => SharedCheckPublicFnInput p yb s ∧ SharedCheckPublicFnInput p yb t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.SharedCheckPublic.code (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) (fun _ _ => True) := by
  let P := fun a : State => ∃ s, SharedCheckPublicFnInput p yb s ∧ a = entered s
  have entry := checkPublicEntry_ct.mono
    (P' := fun (s t : State) => P s ∧ P t ∧ s.sp = t.sp)
    (fun _ _ h => h.2.2) (fun _ _ _ => trivial)
  have wp (a : State) (h : P a) : WP isa (.block VG.Impl.Ffdh.Arm.Domain.CheckPublic.entry) a
      (SharedPublicMainInput p [0, 36, 32, 28, 24] yb) := by
    obtain ⟨s, input, rfl⟩ := h
    refine WP.mono (withAllRest (checkPublicEntry_ok (entered s) input.input.args input.input.incoming
      input.input.domain input.input.domainLength input.input.count input.input.publicValue)) ?_
    rintro u ⟨⟨context, frame⟩, rest⟩
    refine ⟨⟨context, input.input.value.after_frame frame rest (by
      intro r hr
      rw [List.mem_singleton] at hr
      subst r
      exact input.input.valueStack), ?_⟩, input.calls.after rest⟩
    rw [rest.sp]; exact input.input.valueStack
  have body := relCT_chain entry wp wp
    (sharedCheckPublicBody_ct backend (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) length)
  unfold VG.Impl.Ffdh.Arm.SharedCheckPublic.code
  apply framed_ct (fun _ _ h => ⟨h.1.input.stackFits, h.2.1.input.stackFits⟩) (fun _ _ h => h.2.2)
  intro a b tr1 tr2 u v h e1 e2
  obtain ⟨s, t, related, rfl, rfl⟩ := h
  exact body _ _ _ _ _ _ ⟨⟨s, related.1, rfl⟩, ⟨t, related.2.1, rfl⟩,
    by rw [entered_sp, entered_sp, related.2.2]⟩ e1 e2

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/SharedCheckPublicContractCT.lean`, which only this module imported.
section

/-! The native public check has the timing policy of the shared FFDH signature. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

theorem sharedCheckPublic_contract_ct (backend : VG.Proof.Bignum.Arm.MontBackend) : ConstantTime isa (Spec.Ffdh.checkPublicContract abi 176).pre
    (Spec.Ffdh.checkPublicContract abi 176).pub (SharedCheckPublic.code backend) := by
  intro s t tr1 tr2 u v hs ht hp e1 e2
  obtain ⟨p, yb, base, domain, value, count, capacity, domainBytes, valueBytes, inputS⟩ := sharedCheckPublic_data s hs
  have lengths (a : State) (h : (Spec.Ffdh.checkPublicContract abi 176).pre a) :
      (stackArg a 0).toNat = (a.gpr .r2).toNat := by
    sig_pre [Spec.Ffdh.checkPublicContract, Spec.Ffdh.checkPublicSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at h
    exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  sig_pub [Spec.Ffdh.checkPublicContract, Spec.Ffdh.checkPublicSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at hp
  obtain ⟨sp, bytes, p0, p1, p2, p3, _, p5, p6⟩ := hp
  have byteEq := congrArg (List.map (BitVec.ofNat 8)) bytes
  simp only [List.map_append, List.map_map, Function.comp_def, BitVec.ofNat_toNat,
    BitVec.setWidth_eq, List.map_id'] at byteEq
  rw [lengths s hs, lengths t ht, ← p0, ← p1, ← p2, ← p3] at byteEq
  obtain ⟨domEq, yEq⟩ := List.append_inj byteEq
    (by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range])
  have inputT := sharedCheckPublic_input t ht (p := p) (yb := yb)
    (p5.symm.trans base) (p0.symm.trans domain) (p3.symm.trans value)
    (by rw [← p2]; exact count) (by rw [← p6]; exact capacity) ?_ ?_
  · exact (sharedCheckPublicFn_ct backend inputS.input.length s t tr1 tr2 u v ⟨inputS, inputT, sp⟩ e1 e2).1
  · rw [← p1, ← domain]
    change Spec.Rsa.bytesAt t.mem (BitVec.setWidth 64 (s.gpr .r0)) (s.gpr .r1).toNat = p.dom
    rw [← domEq, domain]
    exact domainBytes
  · rw [← value, ← count]
    change Spec.Rsa.bytesAt t.mem (BitVec.setWidth 64 (s.gpr .r3)) (s.gpr .r2).toNat = yb
    rw [← yEq, value, count]
    exact valueBytes

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/SharedCheckPublicSat.lean`, which only this module imported.
section

/-! The enlarged public-check signature remains satisfiable. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

private def sharedPublicSat : State where
  gpr r := match r with | .r0 => 0x1000 | .r1 => 128 | .r2 => 64 | .r3 => 0x2000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8000 then 64 else if a = 0x8005 then 0x30 else
    if a = 0x8008 then 0x20 else if a = 0x8009 then 4 else 0
  rd := [⟨0x1000, 128⟩, ⟨0x2000, 64⟩, ⟨0x8000, 12⟩]
  wr := [⟨0x3000, 8448⟩]

theorem sharedCheckPublic_sat : ∃ s, (Spec.Ffdh.checkPublicContract abi 176).pre s := by
  sig_implies_sat [Spec.Ffdh.checkPublicContract, Spec.Ffdh.checkPublicSig, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid, abi, argRegs, reduceClassify, Loc.val, State.addr]
    [sharedPublicSat, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.Rsa.scratchWords] using sharedPublicSat

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/SharedCheckPublicVerified.lean`, which only this module imported.
section

/-! Shared callable arithmetic retains the existing public-validation contract. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem sharedCheckPublic_verified (b : MontBackend) :
    Verified target (SharedCheckPublic.code b) (Spec.Ffdh.checkPublicContract abi 176) :=
  ⟨sharedCheckPublic_correct b, sharedCheckPublic_contract_ct b, sharedCheckPublic_sat⟩

end VG.Proof.Ffdh.Arm
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.SharedCheckPublic
open VG VG.Arm VG.Proof.Bignum.Arm

def calledCode (b : MontBackend) : Prog isa := b.caller.code (code b)

theorem called_verified (b : MontBackend) :
    Verified target (calledCode b) (Spec.Ffdh.checkPublicContract abi 176) := by
  exact b.caller.verified (sharedCheckPublic_verified b)

theorem called_stack (b : MontBackend) : FrameStack.armStack (calledCode b) ≤ 176 :=
  Nat.le_trans (b.caller.stack_le _) (stack_ok b)

end VG.Proof.Ffdh.Arm.SharedCheckPublic
