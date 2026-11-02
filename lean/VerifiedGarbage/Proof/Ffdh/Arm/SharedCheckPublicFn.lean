module

public import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicFn
public import VerifiedGarbage.Proof.Ffdh.Arm.Frame
public import VerifiedGarbage.Proof.Ffdh.Arm.EntryStore
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
public import VerifiedGarbage.Impl.Ffdh.Arm.SharedCheckPublic
public import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicBody
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Proof.Ffdh.Arm.DomainCallMemory

import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicEntry
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Ffdh.Arm.SharedCheckPublicPublicPower
import VerifiedGarbage.Proof.Ffdh.Arm.ValueChecks
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Impl.Ffdh.Arm.Checks
import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.TCB.Arm.Isa
import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicTail
import VerifiedGarbage.Proof.Ffdh.Arm.QTest
import VerifiedGarbage.Proof.Ffdh.Arm.Branch
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Ffdh.Arm.DomainSharedPrepareAt
import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicMain
import VerifiedGarbage.Proof.Ffdh.Arm.ImportAt
import VerifiedGarbage.Proof.Ffdh.Arm.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ffdh.Arm.Head
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.RelCTAssoc
/-! The native public-value check, from its entry through AAPCS restoration. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/SharedCheckPublicSubgroup.lean`, which only this module imported.
section

/-! Subgroup membership is a native power followed by a fixed-width equality. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt Operand)
open VG.Proof.X25519.Arm (Rest)

theorem sharedCheckPublicSubgroup_ok (backend : MontBackend) (s : State) {p : Inputs} {slots : List Nat} (slot : Nat) {bb : List Byte}
    (h : Context p slots s) (calls : DomainCallMemory p s) (stable : stableSlots slots = true)
    (hb : slot ∈ slots) (h60 : 60 ∈ slots) (h32 : 32 ∈ slots) (hasQ : p.hasQ = true)
    (ready : ArithmeticReady p.base p.len p.w s)
    (modulus : numAt s.mem (State.addr p.base) p.w 0 = p.P) (odd : p.P % 2 = 1)
    (r2 : numAt s.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P)
    (baseBytes : Octets p.base (p.slotValue slot) p.len bb s) (baseLength : bb.length = p.k) :
    WP isa (VG.Impl.Ffdh.Arm.SharedCheckPublic.subgroup (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) slot) s fun t => Context p slots t ∧
      ArithmeticReady p.base p.len p.w t ∧
      t.gpr .r11 = (if Spec.Rsa.powMod (Spec.Rsa.os2ip bb) p.Q p.P = 1 then 1 else 0) ∧
      numAt t.mem (State.addr p.base) p.w 0 = p.P ∧
      numAt t.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P ∧
      Frame [⟨State.addr p.base, 8 * p.len⟩, FrameStack.belowA s.sp 48] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [VG.Impl.Ffdh.Arm.SharedCheckPublic.subgroup, WP.seq_iff]
  refine WP.mono (sharedCheckPublicPublicPower_ok backend s slot 60 32 h calls stable hb h60 h32 h32 ready modulus odd r2 baseBytes baseLength
    (h.qBytes hasQ) (by rw [p.qLength hasQ]; have := p.minLength; omega)
    (by rw [p.qLength hasQ]; have := p.maxLength; omega) (by change BitVec.ofNat 32 p.k = _; rw [p.qLength hasQ])
    (by
      change Region.Disjoint ⟨State.addr p.q, _⟩ _
      rw [p.qLength hasQ]
      exact calls.domainSlice h (by have := p.minLength; omega)
        (by rw [p.domainLength, hasQ]; simp only [ite_true]; omega))) ?_
  rintro u ⟨contextU, readyU, power, modU, r2U, _, frameU, restU⟩
  refine WP.mono (isOne_ok u readyU (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp] : Operand 6) (by decide)) ?_
  rintro t ⟨readyT, flag, arraysT, frameT, restT⟩
  rw [power] at flag
  have frame := frameU.trans (frameT.mono (by simp))
  have rest := restU.trans restT
  exact ⟨h.after_arithmetic calls frame rest readyT.ptr (fun d hd => (stableSlots_at stable hd).1), readyT,
    flag, (arraysT 0 (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide)).trans modU,
    (arraysT 4 (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide)).trans r2U,
    frame, rest⟩

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/SharedCheckPublicTail.lean`, which only this module imported.
section

/-! The optional subgroup check of an imported public value. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)

theorem sharedCheckPublicTail_ok (backend : MontBackend) (s : State) {p : Inputs} {slots : List Nat} {yb : List Byte}
    (h : Context p slots s) (calls : DomainCallMemory p s) (stable : stableSlots slots = true)
    (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) (h36 : 36 ∈ slots) (h60 : 60 ∈ slots)
    (ready : ArithmeticReady p.base p.len p.w s)
    (modulus : numAt s.mem (State.addr p.base) p.w 0 = p.P) (odd : p.P % 2 = 1)
    (r2 : numAt s.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P)
    (value : Octets p.base p.publicValue p.len yb s) (length : yb.length = p.k) :
    WP isa (VG.Impl.Ffdh.Arm.SharedCheckPublic.tail
      (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) s fun t =>
        t.gpr .r0 = publicTailFlag p (Spec.Rsa.os2ip yb) ∧ Frame [⟨State.addr p.base, 8 * p.len⟩, FrameStack.belowA s.sp 48] s.mem t.mem := by
  rw [VG.Impl.Ffdh.Arm.SharedCheckPublic.tail, VG.Impl.Ffdh.Arm.Domain.withQ, WP.seq_iff]
  refine WP.mono (qTest_ok s h h28 h32) ?_
  rintro u ⟨⟨zero, memU⟩, restU⟩
  have frameU : Frame [⟨State.addr p.base, 8 * p.len⟩] s.mem u.mem := by rw [memU]; exact Frame.refl _ _
  have ptrU := (restU.gpr .r0 (by simp)).trans ready.ptr
  have readyU := ready.of_mem memU restU ptrU
  have contextU := h.after_workspace frameU restU ptrU (fun d hd => (stableSlots_at stable hd).1)
  have valueU := value.after_workspace frameU restU
  refine WP.ite p.hasQ (by simp only [eval, zero, Bool.not_not]) ?_ ?_
  · intro hasQ
    rw [WP.seq_iff]
    refine WP.mono (sharedCheckPublicSubgroup_ok backend u 36 contextU (calls.after restU) stable h36 h60 h32 hasQ readyU
      (by rw [memU]; exact modulus) odd (by rw [memU]; exact r2) valueU length) ?_
    rintro v ⟨_, _, flag, _, _, frameV, _⟩
    refine WP.mono (finishFlag_ok v) ?_
    rintro t ⟨⟨result, memT⟩, _⟩
    refine ⟨?_, ?_⟩
    · rw [result, flag]
      exact (ite_eq_left hasQ).symm
    · rw [memT]; exact (frameU.mono (by simp)).trans (by simpa only [restU.sp] using frameV)
  · intro hasQ
    refine WP.mono (ret_ok u 1 (by decide)) ?_
    rintro t ⟨⟨result, memT⟩, _⟩
    refine ⟨?_, ?_⟩
    · rw [result]
      exact (ite_eq_right (by rw [hasQ]; decide)).symm
    · rw [memT]; exact frameU.mono (by simp)

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/SharedCheckPublicMain.lean`, which only this module imported.
section

/-! Complete native range and subgroup checks of an imported public value. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt Operand arrAt)

theorem sharedCheckPublicMain_ok (backend : MontBackend) (s : State) {p : Inputs} {slots : List Nat} {yb : List Byte}
    (h : Context p slots s) (calls : DomainCallMemory p s) (stable : stableSlots slots = true)
    (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots)
    (h36 : 36 ∈ slots) (h60 : 60 ∈ slots)
    (large : 1 < p.P) (odd : p.P % 2 = 1)
    (value : Octets p.base p.publicValue p.len yb s) (length : yb.length = p.k)
    (valueStack : Region.Disjoint ⟨State.addr p.publicValue, yb.length⟩ ⟨State.addr s.sp, 72⟩) :
    WP isa (VG.Impl.Ffdh.Arm.SharedCheckPublic.main (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) s fun t =>
      t.gpr .r0 = publicFlag p (Spec.Rsa.os2ip yb) ∧ Frame (domainPrepareWrites p s) s.mem t.mem := by
  have op0 : Operand 0 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op1 : Operand 1 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have extend {m m' : Mem} (f : Frame [⟨State.addr p.base, 8 * p.len⟩] m m') : Frame (domainPrepareWrites p s) m m' :=
    f.mono (by intro r hr; rw [List.mem_singleton] at hr; subst r; simp [domainPrepareWrites, prepareAtWrites, prepareWrites])
  rw [VG.Impl.Ffdh.Arm.SharedCheckPublic.main, WP.seq_iff]
  refine WP.mono (domainSharedPrepareAt24_ok backend s h calls stable h0 h24 h32 large odd) ?_
  rintro u ⟨contextU, readyU, modU, r2U, frameU, restU⟩
  have valueU := value.after_frame frameU restU (by
    intro r hr
    simp only [domainPrepareWrites, prepareAtWrites, prepareWrites, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl) | rfl
    · exact value.separate
    · exact valueStack.sub_right (Offset.sub_base _ (by decide))
    · exact valueStack.sub_right (Offset.sub_base _ (by decide))
    · rw [length]; exact calls.publicValue)
  rw [WP.seq_iff]
  refine WP.mono (importAt_ok u 1 36 32 contextU stable h36 h32 readyU (by decide) (by decide)
    valueU (by rw [length]; have := p.minLength; omega) (by rw [length]; exact p.width.2.2.2.1)
    (by change BitVec.ofNat 32 p.k = _; rw [length])) ?_
  rintro v ⟨contextV, readyV, y, keepsV, frameV, restV⟩
  have bound : arrAt p.w 8 ≤ 8 * p.len := readyV.width ▸ readyV.layout.2.2.1
  have modV := (keeps_array_num keepsV bound op0 (by decide : 0 ≠ 1)).trans modU
  have r2V := (keeps_array_num keepsV bound op4 (by decide : 4 ≠ 1)).trans r2U
  rw [WP.seq_iff]
  refine WP.mono (inRange_ok v readyV op1 (by decide) (by rw [modV]; exact odd)) ?_
  rintro w ⟨readyW, flag, arraysW, frameW, restW⟩
  rw [y, modV] at flag
  change w.gpr .r11 = (if 1 < Spec.Rsa.os2ip yb ∧ Spec.Rsa.os2ip yb < p.P - 1 then 1 else 0) at flag
  have contextW := contextV.after_workspace frameW restW readyW.ptr (fun d hd => (stableSlots_at stable hd).1)
  have modW := (arraysW 0 op0 (by decide)).trans modV
  have r2W := (arraysW 4 op4 (by decide)).trans r2V
  have valueW := (valueU.after_workspace frameV restV).after_workspace frameW restW
  have frameW' := (frameU.trans (extend frameV)).trans (extend frameW)
  rw [VG.Impl.Ffdh.Arm.Domain.ifFlag, WP.seq_iff]
  refine WP.mono (testFlag_ok w) ?_
  rintro z ⟨⟨zero, memZ⟩, restZ⟩
  by_cases valid : 1 < Spec.Rsa.os2ip yb ∧ Spec.Rsa.os2ip yb < p.P - 1
  · refine WP.ite true (by change some (!z.z) = some true; rw [zero, flag, ite_eq_left valid]; rfl) ?_ (by intro hf; cases hf)
    intro _
    have frameZ : Frame [⟨State.addr p.base, 8 * p.len⟩] w.mem z.mem := by rw [memZ]; exact Frame.refl _ _
    have ptrZ := (restZ.gpr .r0 (by simp)).trans readyW.ptr
    have contextZ := contextW.after_workspace frameZ restZ ptrZ (fun d hd => (stableSlots_at stable hd).1)
    have readyZ := readyW.of_mem memZ restZ ptrZ
    refine WP.mono (sharedCheckPublicTail_ok backend z contextZ ((calls.after restU).after restV |>.after restW |>.after restZ) stable h28 h32 h36 h60 readyZ
      (by rw [memZ]; exact modW) odd (by rw [memZ]; exact r2W)
      (valueW.after_workspace frameZ restZ) length) ?_
    rintro t ⟨result, frameT⟩
    refine ⟨?_, ?_⟩
    · rw [publicFlag, ite_eq_left valid]; exact result
    · rw [memZ] at frameT
      apply frameW'.trans
      rw [restZ.sp, restW.sp, restV.sp, restU.sp] at frameT
      exact frameT.mono (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        simp only [domainPrepareWrites, prepareAtWrites, prepareWrites, List.mem_append,
          List.mem_cons, List.not_mem_nil, or_false]
        rcases hr with rfl | rfl
        · exact Or.inl (Or.inl rfl)
        · exact Or.inr rfl)
  · refine WP.ite false (by change some (!z.z) = some false; rw [zero, flag, ite_eq_right valid]; rfl) (by intro ht; cases ht) ?_
    intro _
    refine WP.mono (ret_ok z 0 (by decide)) ?_
    rintro t ⟨⟨result, memT⟩, _⟩
    refine ⟨?_, ?_⟩
    · rw [publicFlag, ite_eq_right valid]; exact result
    · rw [memT, memZ]; exact frameW'

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/SharedCheckPublicBody.lean`, which only this module imported.
section

/-! The entire imported-public-value body, including invalid public moduli. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont

def sharedPublicBodyWrites (p : Inputs) (s : State) : List Region :=
  bodyWrites p s ++ [FrameStack.belowA s.sp 48]

theorem sharedCheckPublicBody_ok (backend : MontBackend) (s : State) {p : Inputs} {slots : List Nat} {yb : List Byte}
    (h : Context p slots s) (calls : DomainCallMemory p s) (stable : stableSlots slots = true)
    (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) (h36 : 36 ∈ slots)
    (value : Octets p.base p.publicValue p.len yb s) (length : yb.length = p.k)
    (valueStack : Region.Disjoint ⟨State.addr p.publicValue, yb.length⟩ ⟨State.addr s.sp, 72⟩) :
    WP isa (VG.Impl.Ffdh.Arm.Domain.head (VG.Impl.Ffdh.Arm.SharedCheckPublic.main (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul))) s fun t =>
      t.gpr .r0 = checkedPublicFlag p (Spec.Rsa.os2ip yb) ∧ Frame (sharedPublicBodyWrites p s) s.mem t.mem := by
  unfold VG.Impl.Ffdh.Arm.Domain.head
  apply WP.assoc
  rw [WP.seq_iff]
  refine WP.mono (head_ok s h stable h0 h24 h32) ?_
  rintro u ⟨contextU, zero, frameU, restU⟩
  have fU : Frame (sharedPublicBodyWrites p s) s.mem u.mem := frameU.mono (by simp [sharedPublicBodyWrites, bodyWrites])
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
    refine WP.mono (sharedCheckPublicMain_ok backend u contextU (calls.after restU) stableU
      (by simp [h0]) (by simp [h24]) (by simp [h28]) (by simp [h32]) (by simp [h36]) (by simp)
      facts.2.1 facts.1 valueU length valueStackU) ?_
    rintro t ⟨result, frameT⟩
    refine ⟨?_, fU.trans (frameT.sub ?_)⟩
    · rw [checkedPublicFlag, ite_eq_left valid]; exact result
    · intro r hr
      simp only [domainPrepareWrites, prepareAtWrites, prepareWrites, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with (rfl | rfl | rfl) | rfl
      · exact ⟨⟨State.addr p.base, 8 * p.len⟩, by simp [sharedPublicBodyWrites, bodyWrites], by intro a ha; exact ha⟩
      · refine ⟨⟨State.addr s.sp, 72⟩, by simp [sharedPublicBodyWrites, bodyWrites], ?_⟩
        rw [restU.sp]
        exact Offset.sub_base _ (by decide)
      · refine ⟨⟨State.addr s.sp, 72⟩, by simp [sharedPublicBodyWrites, bodyWrites], ?_⟩
        rw [restU.sp]
        exact Offset.sub_base _ (by decide)
      · refine ⟨FrameStack.belowA s.sp 48, by simp [sharedPublicBodyWrites], ?_⟩
        rw [restU.sp]
        intro a ha; exact ha
  · have invalid : Spec.Rsa.modulusValid p.P p.k = false := Bool.eq_false_iff.mpr valid
    refine WP.ite false (by change some u.z = some false; rw [zero, invalid]) (by intro ht; cases ht) ?_
    intro _
    refine WP.mono (ret_ok u 0 (by decide)) ?_
    rintro t ⟨⟨result, memT⟩, _⟩
    refine ⟨?_, ?_⟩
    · rw [checkedPublicFlag, ite_eq_right valid]; exact result
    · rw [memT]; exact fU

end VG.Proof.Ffdh.Arm
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont

theorem sharedCheckPublicEntered_ok (backend : MontBackend) (s : State) {p : Inputs} {yb : List Byte}
    (h : ArgumentMemory p [] s) (incoming : IncomingScratch p s) (calls : DomainCallMemory p s)
    (domain : s.gpr .r0 = p.domain) (domainLength : s.gpr .r1 = BitVec.ofNat 32 p.dom.length)
    (count : s.gpr .r2 = BitVec.ofNat 32 p.k) (publicValue : s.gpr .r3 = p.publicValue)
    (value : Octets p.base p.publicValue p.len yb s) (length : yb.length = p.k)
    (valueStack : Region.Disjoint ⟨State.addr p.publicValue, yb.length⟩ ⟨State.addr s.sp, 72⟩) :
    WP isa (.seq (.block VG.Impl.Ffdh.Arm.Domain.CheckPublic.entry)
      (VG.Impl.Ffdh.Arm.Domain.head (VG.Impl.Ffdh.Arm.SharedCheckPublic.main (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)))) s fun t =>
      t.gpr .r0 = checkedPublicFlag p (Spec.Rsa.os2ip yb) ∧ Frame (sharedPublicBodyWrites p s) s.mem t.mem := by
  rw [WP.seq_iff]
  refine WP.mono (withAllRest (checkPublicEntry_ok s h incoming domain domainLength count publicValue)) ?_
  rintro u ⟨⟨contextU, frameU⟩, restU⟩
  have valueU := value.after_frame frameU restU (by
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    exact valueStack)
  have valueStackU : Region.Disjoint ⟨State.addr p.publicValue, yb.length⟩ ⟨State.addr u.sp, 72⟩ := by
    rw [restU.sp]; exact valueStack
  refine WP.mono (sharedCheckPublicBody_ok backend u contextU (calls.after restU) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) valueU length valueStackU) ?_
  rintro t ⟨result, frameT⟩
  refine ⟨result, ?_⟩
  have entryFrame : Frame (sharedPublicBodyWrites p s) s.mem u.mem := frameU.mono (by simp [sharedPublicBodyWrites, bodyWrites])
  change Frame [⟨State.addr p.base, 8 * p.len⟩, ⟨State.addr u.sp, 72⟩, FrameStack.belowA u.sp 48] u.mem t.mem at frameT
  rw [restU.sp] at frameT
  exact entryFrame.trans frameT

structure SharedCheckPublicFnInput (p : Inputs) (yb : List Byte) (s : State) : Prop where
  input : CheckPublicFnInput p yb s
  calls : DomainCallMemory p (entered s)
  saved : ∀ r ∈ sharedPublicBodyWrites p (entered s),
    (⟨State.addr (pcPushed s).sp, 56⟩ : Region).Disjoint r

theorem sharedCheckPublicFn_ok (backend : MontBackend) (s : State) {p : Inputs} {yb : List Byte} (h : SharedCheckPublicFnInput p yb s) :
    WP isa (VG.Impl.Ffdh.Arm.SharedCheckPublic.code (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) s fun t =>
      abiPreserved s t ∧ t.gpr .r0 = checkedPublicFlag p (Spec.Rsa.os2ip yb) := by
  unfold VG.Impl.Ffdh.Arm.SharedCheckPublic.code
  refine framed_of_separate _ s h.input.stackFits (sharedPublicBodyWrites p (entered s))
    (fun _ status => status = checkedPublicFlag p (Spec.Rsa.os2ip yb)) h.saved ?_
  refine WP.mono (sharedCheckPublicEntered_ok backend (entered s) h.input.args h.input.incoming h.calls h.input.domain h.input.domainLength
    h.input.count h.input.publicValue h.input.value h.input.length h.input.valueStack) ?_
  rintro t ⟨result, frame⟩
  exact ⟨frame, result⟩

end VG.Proof.Ffdh.Arm
