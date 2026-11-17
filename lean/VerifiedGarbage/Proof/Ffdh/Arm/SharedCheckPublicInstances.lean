module

public import VerifiedGarbage.Spec.Ffdh.Contract
import VerifiedGarbage.Proof.Ffdh.Arm.SubgroupCT
public import VerifiedGarbage.Proof.Ffdh.Arm.DomainCallMemory
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Impl.Ffdh.Arm.SharedCheckPublic
public import VerifiedGarbage.Proof.Ffdh.Arm.PowerAtCT
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomeryCT
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomery
import VerifiedGarbage.Proof.Ffdh.Arm.PublicPowerInput
import VerifiedGarbage.Proof.Ffdh.Arm.PublicScanCT
import VerifiedGarbage.Proof.Ffdh.Arm.KeyPowerCT
import VerifiedGarbage.Proof.Ffdh.Arm.PowerArgs
import VerifiedGarbage.Proof.Bignum.Arm.SharedWindowPhaseCT
import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Ffdh.Arm.ValueChecksCT
import VerifiedGarbage.Proof.Bignum.Arm.TwoExpSharedCT
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
public import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicMainCT
import VerifiedGarbage.Proof.Ffdh.Arm.BranchCT
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.QTest
import VerifiedGarbage.Proof.Ffdh.Arm.Context
public import VerifiedGarbage.Impl.Ffdh.Arm.SharedPrepare
import VerifiedGarbage.Proof.Ffdh.Arm.DomainSharedPrepareAt
public import VerifiedGarbage.Proof.Ffdh.Arm.Prepare
import VerifiedGarbage.Proof.Ffdh.Arm.PrepareCT
import VerifiedGarbage.Impl.Bignum.Arm.SharedPrecompute
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeState
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeCT
import VerifiedGarbage.Proof.Bignum.Arm.SharedR2CT
import VerifiedGarbage.Proof.Bignum.Arm.ImportModulus
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeInverse
public import VerifiedGarbage.Impl.Bignum.Arm.MontCall
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
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicEntryCT
import VerifiedGarbage.Proof.Ffdh.Arm.FrameCT
import VerifiedGarbage.Proof.Ffdh.Arm.Entered
public import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicFn
import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicSpec
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig
import Init.Data.BitVec.Basic
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.Lit
import Batteries.Logic
import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicPre
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Ffdh.Arm.Frame
public import VerifiedGarbage.Proof.Ffdh.Arm.EntryStore
public import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicBody
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Ffdh.Arm.ValueChecks
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Impl.Ffdh.Arm.Checks
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicMain
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
public import VerifiedGarbage.Impl.Ffdh.Arm.Arithmetic
public import VerifiedGarbage.Proof.Ffdh.Arm.Octets
import VerifiedGarbage.Proof.Bignum.Arm.SharedWindowPhase
import VerifiedGarbage.Proof.Bignum.Arm.TwoExpShared

/-! ### `Ffdh.Arm.SharedCheckPublicPre`, which only this module used -/

section

/-! ### `Ffdh.Arm.SharedCheckPublicFn`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.SharedCheckPublicPublicPower`, which this module and modules that import it used -/

section

/-! A power from saved FFDH base and exponent buffers. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

theorem sharedCheckPublicPublicPower_ok (backend : MontBackend) (s : State) {p : Inputs} {slots : List Nat} (bs es ec : Nat)
    {bb eb : List Byte} {M : Nat} (h : Context p slots s) (calls : DomainCallMemory p s) (stable : stableSlots slots = true)
    (hb : bs ∈ slots) (he : es ∈ slots) (hc : ec ∈ slots) (hk : 32 ∈ slots)
    (ready : ArithmeticReady p.base p.len p.w s)
    (modulus : numAt s.mem (State.addr p.base) p.w 0 = M) (odd : M % 2 = 1)
    (r2 : numAt s.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % M)
    (baseBytes : Octets p.base (p.slotValue bs) p.len bb s) (baseLength : bb.length = p.k)
    (exponentBytes : Octets p.base (p.slotValue es) p.len eb s) (exponentPositive : 0 < eb.length)
    (exponentFits : eb.length < 2 ^ 32) (exponentLength : p.slotValue ec = BitVec.ofNat 32 eb.length)
    (exponentBelow : Region.Disjoint ⟨State.addr (p.slotValue es), eb.length⟩ (FrameStack.belowA s.sp 48)) :
    WP isa (VG.Impl.Ffdh.Arm.SharedCheckPublic.publicPowerAt
      (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) bs es ec) s fun t => Context p slots t ∧
      ArithmeticReady p.base p.len p.w t ∧
      numAt t.mem (State.addr p.base) p.w 6 = Spec.Rsa.powMod (Spec.Rsa.os2ip bb) (Spec.Rsa.os2ip eb) M ∧
      numAt t.mem (State.addr p.base) p.w 0 = M ∧
      numAt t.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % M ∧
      numAt t.mem (State.addr p.base) p.w 7 = 1 ∧
      Frame [⟨State.addr p.base, 8 * p.len⟩, FrameStack.belowA s.sp 48] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [VG.Impl.Ffdh.Arm.SharedCheckPublic.publicPowerAt, WP.seq_iff]
  refine WP.mono (powerArgs_ok s bs es ec h stable hb he hc hk) ?_
  rintro u ⟨⟨source, count, exponent, exponentCount, mem⟩, restU⟩
  have frameU : Frame [⟨State.addr p.base, 8 * p.len⟩] s.mem u.mem := by rw [mem]; exact Frame.refl _ _
  have readyU := ready.of_mem mem restU ((restU.gpr .r0 (by simp)).trans ready.ptr)
  have baseU := baseBytes.after_workspace frameU restU
  have exponentU := exponentBytes.after_workspace frameU restU
  have input : PowerInput p.base (p.slotValue bs) (p.slotValue es) p.len p.w M bb eb u :=
    ⟨readyU, by rw [mem]; exact modulus, odd, by rw [mem]; exact r2,
      baseU, exponentU, by rw [baseLength]; have := p.minLength; omega_using [this],
      by rw [baseLength]; exact p.width.2.2.2.1, exponentPositive, exponentFits,
      source, by rw [baseLength]; exact count, exponent, exponentCount.trans exponentLength⟩
  rw [WP.seq_iff]
  refine WP.mono (PublicScan.input_ok u input) ?_
  rintro scanT ⟨inputT,memScan,restScan⟩
  rw [WP.seq_iff]
  refine WP.mono (powerImport_ok scanT inputT) ?_
  rintro v ⟨phaseInput, frameV, restV⟩
  let K := TwoExp.sharedMontgomery p.base s.sp p.len p.w backend.name backend.mul
    (fun _ _ _ ho ha hb z hi => backend.correct z hi ho ha hb) backend.stackOk
  have spV : v.sp = s.sp := restV.sp.trans (restScan.sp.trans restU.sp)
  have separate : ∀ r ∈ [⟨State.addr p.base, 8 * p.len⟩, FrameStack.belowA s.sp 48],
      Region.Disjoint ⟨State.addr (p.slotValue es + BitVec.ofNat 32 (VG.Proof.Ffdh.lead eb)), (eb.drop (VG.Proof.Ffdh.lead eb)).length⟩ r := by
    intro r hr
    rcases List.mem_cons.mp hr with hr | hr
    · subst r; exact inputT.exponentBytes.separate
    · have eq := List.mem_singleton.mp hr; subst r; exact PublicScan.suffix_separate exponentBytes exponentPositive exponentBelow
  refine WP.mono (sharedWindowExpPhase_ok K v phaseInput
    ⟨(((calls.after restU).after restScan).after restV).stack, spV⟩ p.width.2.2.1 separate) ?_
  rintro t ⟨readyT, value, modT, r2T, oneT, _, frameT, restT⟩
  have initial : Frame [⟨State.addr p.base, 8 * p.len⟩, FrameStack.belowA s.sp 48] s.mem v.mem :=
    (frameU.trans (show Frame [⟨State.addr p.base,8*p.len⟩] u.mem scanT.mem from
      by rw [memScan];exact Frame.refl _ _)).trans frameV |>.mono (by simp)
  have frame := initial.trans frameT
  have rest : Rest roundClobbers s t :=
    (((restU.mono (by simp [roundClobbers])).trans (restScan.mono (by simp [roundClobbers]))).trans restV).trans restT
  exact ⟨h.after_arithmetic calls frame rest readyT.ptr (fun d hd => (stableSlots_at stable hd).1),
    readyT, by simpa only [VG.Proof.Ffdh.os2ip_drop_lead] using value, modT, r2T, oneT, frame, rest⟩

end VG.Proof.Ffdh.Arm

end

end

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

end

end

/-! The public-check signature reserves the outer frame and shared-call stack. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Arm.FrameStack VG.Proof.Bignum.Arm

theorem sharedCheckPublic_pre128 (s : State) (pre : (Spec.Ffdh.checkPublicContract abi 176).pre s) :
    (Spec.Ffdh.checkPublicContract abi 128).pre s := by
  sig_pre [Spec.Ffdh.checkPublicContract, Spec.Ffdh.checkPublicSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at pre ⊢
  obtain ⟨stackFit, argFit, rd, wr, domS, yS, sArgs, stackDom, stackY, stackS, stackArgs,
    domFit, yFit, sFit, bounds, domainLen, yLen, space⟩ := pre
  have inner : Region.Sub ⟨State.addr s.sp - BitVec.ofNat 64 128, 128⟩
      ⟨State.addr s.sp - BitVec.ofNat 64 176, 176⟩ :=
    Offset.below_mono _ (by decide) (by decide)
  exact ⟨by omega_using [stackFit], argFit, rd, wr, domS, yS, sArgs, stackDom.sub_left inner,
    stackY.sub_left inner, stackS.sub_left inner, stackArgs.sub_left inner,
    domFit, yFit, sFit, bounds, domainLen, yLen, space⟩

theorem sharedCheckPublic_input (s : State) (pre : (Spec.Ffdh.checkPublicContract abi 176).pre s)
    {p : Inputs} {yb : List Byte}
    (base : stackArg s 1 = p.base) (domain : s.gpr .r0 = p.domain) (publicValue : s.gpr .r3 = p.publicValue)
    (count : (s.gpr .r2).toNat = p.k) (capacity : (stackArg s 2).toNat = p.len)
    (domainBytes : Spec.Rsa.bytesAt s.mem (State.addr p.domain) (s.gpr .r1).toNat = p.dom)
    (publicBytes : Spec.Rsa.bytesAt s.mem (State.addr p.publicValue) p.k = yb) :
    SharedCheckPublicFnInput p yb s := by
  have old := checkPublic_input s (sharedCheckPublic_pre128 s pre) base domain publicValue count capacity domainBytes publicBytes
  sig_pre [Spec.Ffdh.checkPublicContract, Spec.Ffdh.checkPublicSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at pre
  obtain ⟨stackFit, _, _, _, _, _, _, stackDom, stackY, stackS, _, _, _, _, _, _, yLen, _⟩ := pre
  have domLen : (s.gpr .r1).toNat = p.dom.length := by
    have eq := congrArg List.length domainBytes
    simpa only [VG.Proof.Bignum.bytesAt_length] using eq
  rw [yLen,count,publicValue] at stackY
  rw [domain,domLen] at stackDom
  rw [base,capacity,Nat.mul_comm p.len 8] at stackS
  have reserved : State.addr s.sp - BitVec.ofNat 64 176 = State.addr (s.sp - BitVec.ofNat 32 176) :=
    (addr_sub' stackFit).symm
  simp only [State.addr] at reserved
  rw [reserved] at stackDom stackY stackS
  have calls := DomainCallMemory.of_outer stackFit (entered_sp s) stackS stackDom.symm stackY.symm
  refine ⟨old,calls,?_⟩
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact old.saved r hr
  · have eq := List.mem_singleton.mp hr
    subst r
    have shifted : (pcPushed s).sp = (entered s).sp + BitVec.ofNat 32 72 := (BitVec.sub_add_cancel _ _).symm
    have fit : (entered s).sp.toNat + 72 < 2^32 := by
      rw [entered_nat s (by omega_using [stackFit])]; have := s.sp.isLt; omega_using []
    rw [shifted,VG.Arm.addr_add fit,belowA,addr_sub' calls.stack.fit]
    exact (Offset.disjoint_below_above _ (m:=48) (a:=72) (l:=56) (by decide)).symm

end VG.Proof.Ffdh.Arm

end

end

/-! ### `Ffdh.Arm.SharedCheckPublicPrograms`, which only this module used -/

section

/-! One public-key validation program for every shared Montgomery backend. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.SharedCheckPublic
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Bignum.Arm

def code (b : MontBackend) : Prog isa :=
  VG.Impl.Ffdh.Arm.SharedCheckPublic.code (MontCall.op b.name b.mul)

end VG.Proof.Ffdh.Arm.SharedCheckPublic

end

end

/-! ### `Ffdh.Arm.SharedCheckPublicPublicPowerCT`, which only this module used -/

section

/-! Shared subgroup exponentiation trims only the public exponent prefix. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

private theorem sharedPublicPower_ct {base src ep : BitVec 32} {len w M : Nat}
    {P : State → Prop} {regions : List Region} {bb eb1 eb2 : List Byte}
    (K : TwoExp.Montgomery base len w P regions) (ct : TwoExp.MontgomeryTiming K)
    (fits : Proof.Rsa.Mont.arrAt w 16 ≤ 8 * len) (positive : 0 < eb1.length)
    (length : eb1.length = eb2.length)
    (separate : ∀ r ∈ regions, Region.Disjoint ⟨State.addr ep, eb1.length⟩ r) :
    RelCT isa (fun s t => KeyPower.Input base src ep len w M P regions bb eb1 s ∧
      KeyPower.Input base src ep len w M P regions bb eb2 t ∧ s.sp = t.sp)
      (.seq VG.Impl.Ffdh.Arm.powerImport (VG.Impl.Bignum.Arm.SharedWindow.phase K.op))
      (fun _ _ => True) := by
  exact relCT_chain
    ((KeyPower.import_ct length).mono
      (fun _ _ h => ⟨h.1.power, h.2.1.power, h.2.2⟩) (fun _ _ h => h))
    (fun s h => WP.mono (KeyPower.import_ok K s h) fun _ k => ⟨k.1.phase, k.1.persistent⟩)
    (fun s h => WP.mono (KeyPower.import_ok K s h) fun _ k => ⟨k.1.phase, k.1.persistent⟩)
    (SharedWindow.phase_ct K ct fits positive length separate)

theorem sharedCheckPublicPublicPower_ct {p : Inputs} {slots : List Nat} {bs es ec M : Nat}
    {bb eb : List Byte} {P : State → Prop} {regions : List Region}
    (K : TwoExp.Montgomery p.base p.len p.w P regions) (ct : TwoExp.MontgomeryTiming K)
    (stable : stableSlots slots = true) (hb : bs ∈ slots) (he : es ∈ slots)
    (hc : ec ∈ slots) (hk : 32 ∈ slots)
    (baseLength : bb.length = p.k) (positive : 0 < eb.length) (fit : eb.length < 2^32)
    (count : p.slotValue ec = BitVec.ofNat 32 eb.length) (odd : M % 2 = 1)
    (separate : ∀ r ∈ regions, Region.Disjoint ⟨State.addr (p.slotValue es),eb.length⟩ r) :
    RelCT isa (fun s t => (PowerAtInput p slots bs es M bb eb s ∧ P s) ∧
      (PowerAtInput p slots bs es M bb eb t ∧ P t) ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.SharedCheckPublic.publicPowerAt K.op bs es ec) (fun _ _ => True) := by
  intro s0 t0 tr1 tr2 u v initial run1 run2
  have leadLt := VG.Proof.Ffdh.lead_lt (bs := eb) (by intro empty; rw [empty] at positive; simp at positive)
  have trimmedPositive : 0 < (eb.drop (VG.Proof.Ffdh.lead eb)).length := by
    simp only [List.length_drop]; omega_using [leadLt]
  have args (s : State) (h : PowerAtInput p slots bs es M bb eb s ∧ P s) :
      WP isa (.block (VG.Impl.Ffdh.Arm.Domain.powerArgs bs es ec)) s
        (KeyPower.Input p.base (p.slotValue bs) (p.slotValue es) p.len p.w M P regions bb eb) := by
    obtain ⟨tr,u,run,input⟩ := powerArgs_input s stable hb he hc hk baseLength positive fit count odd h.1
    obtain ⟨_,v,run',values,rest⟩ := powerArgs_ok s bs es ec h.1.context stable hb he hc hk
    obtain ⟨_,rfl⟩ := Exec.det run run'
    have frame : Frame [⟨State.addr p.base,8*p.len⟩] s.mem u.mem := by
      rw [values.2.2.2.2]; exact Frame.refl _ _
    exact ⟨tr,u,run,input,K.stable frame (rest.mono (by simp [roundClobbers])) h.2,separate⟩
  have trim (s : State)
      (h : KeyPower.Input p.base (p.slotValue bs) (p.slotValue es) p.len p.w M P regions bb eb s) :
      WP isa VG.Impl.Ffdh.Arm.PublicScan.code s
        (KeyPower.Input p.base (p.slotValue bs)
          (p.slotValue es+BitVec.ofNat 32 (VG.Proof.Ffdh.lead eb)) p.len p.w M P regions bb
            (eb.drop (VG.Proof.Ffdh.lead eb))) := by
    refine WP.mono (PublicScan.input_ok s h.power) ?_
    rintro t ⟨input,mem,rest⟩
    have frame : Frame [⟨State.addr p.base,8*p.len⟩] s.mem t.mem := by
      rw [mem]; exact Frame.refl _ _
    exact ⟨input,K.stable frame (rest.mono (by simp [roundClobbers])) h.persistent,
      fun r hr => PublicScan.suffix_separate h.power.exponentBytes positive (h.separate r hr)⟩
  have scan := (PublicScan.code_ct positive fit).mono
    (P' := fun (s t : State) => KeyPower.Input p.base (p.slotValue bs) (p.slotValue es) p.len p.w M P regions bb eb s ∧
      KeyPower.Input p.base (p.slotValue bs) (p.slotValue es) p.len p.w M P regions bb eb t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨⟨h.1.power.exponentBytes,h.1.power.exponent,h.1.power.exponentCount⟩,
      ⟨h.2.1.power.exponentBytes,h.2.1.power.exponent,h.2.1.power.exponentCount⟩,h.2.2⟩)
    (fun _ _ h => h)
  have trimmedSeparate : ∀ r ∈ regions, Region.Disjoint
      ⟨State.addr (p.slotValue es+BitVec.ofNat 32 (VG.Proof.Ffdh.lead eb)),
        (eb.drop (VG.Proof.Ffdh.lead eb)).length⟩ r := by
    intro r hr
    exact PublicScan.suffix_separate initial.1.1.exponent positive (separate r hr)
  have tail := relCT_chain scan trim trim
    (sharedPublicPower_ct K ct p.width.2.2.1 trimmedPositive rfl trimmedSeparate)
  unfold VG.Impl.Ffdh.Arm.SharedCheckPublic.publicPowerAt at run1 run2
  exact (relCT_chain ((powerArgs_ct bs es ec).mono (fun _ _ h => h.2.2) (fun _ _ _ => trivial))
    (fun s h => args s h) (fun s h => args s h) tail) s0 t0 tr1 tr2 u v initial run1 run2

end VG.Proof.Ffdh.Arm

end

end

/-! ### `Ffdh.Arm.SharedCheckPublicStateCT`, which only this module used -/

section

/-! Persistent call memory accompanies the existing public-value timing states. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

structure SharedSubgroupInput (p : Inputs) (slots : List Nat) (slot : Nat) (bb : List Byte)
    (s : State) : Prop extends SubgroupInput p slots slot bb s where
  calls : DomainCallMemory p s

structure SharedPublicMainInput (p : Inputs) (slots : List Nat) (yb : List Byte)
    (s : State) : Prop extends PublicMainInput p slots yb s where
  calls : DomainCallMemory p s

structure SharedPublicImported (p : Inputs) (slots : List Nat) (yb : List Byte)
    (s : State) : Prop extends PublicImported p slots yb s where
  calls : DomainCallMemory p s

structure SharedPublicRanged (p : Inputs) (slots : List Nat) (yb : List Byte)
    (s : State) : Prop extends PublicRanged p slots yb s where
  calls : DomainCallMemory p s

end VG.Proof.Ffdh.Arm

end

end

/-! ### `Ffdh.Arm.SharedPrepareCT`, which only this module used -/

section

/-! # FFDH setup uses shared constant-time Montgomery precomputation -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/SharedPrecomputeCT.lean`, which only this module imported.
section

/-! # Shared modulus precomputation has a public trace -/

section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem sharedPrecompute_ct {base src : BitVec 32} {len w k : Nat}
    {P : State → Prop} {regions : List Region}
    (K : TwoExp.Montgomery base len w P regions) (ct : TwoExp.MontgomeryTiming K)
    (countFits : 128 * w < 2 ^ 32) :
    RelCT isa (fun s t => (PrecomputeInput base src len w k s ∧ P s) ∧
      (PrecomputeInput base src len w k t ∧ P t) ∧ s.sp = t.sp)
      (SharedPrecompute.precompute K.op) (fun _ _ => True) := by
  have imported (s : State) (h : PrecomputeInput base src len w k s ∧ P s) :
      WP isa importModulus s fun t => PrecomputeModulus base len w t ∧ P t := by
    refine (importModulus_ready s h.1).and ?_
    refine WP.mono (importModulus_ok s h.1.workspace h.1.layout h.1.width h.1.positive h.1.fits h.1.sourceFits
      h.1.readable h.1.separate h.1.ptr h.1.source h.1.count h.1.stackRead h.1.stackSep h.1.saved) ?_
    rintro t ⟨_, _, _, _, frame, rest⟩
    exact K.stable frame rest h.2
  have inverse (s : State) (h : PrecomputeModulus base len w s ∧ P s) :
      WP isa precomputeInverse s fun t => ArithmeticReady base len w t ∧ P t := by
    refine (precomputeInverse_ready s h.1).and ?_
    refine WP.mono (precomputeInverse_ok s h.1.workspace h.1.layout h.1.width h.1.ptr h.1.odd h.1.large
      h.1.stackRead h.1.stackSep h.1.saved) ?_
    rintro t ⟨_, _, frame, rest⟩
    exact K.stable frame rest h.2
  unfold SharedPrecompute.precompute
  refine relCT_chain ((importModulus_ct (base := base) (src := src) (len := len) (w := w) (k := k)).mono
    (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ h => h)) imported imported ?_
  exact relCT_chain ((precomputeInverse_ct (base := base) (len := len) (w := w)).mono
    (fun _ _ h => ⟨h.1.1, h.2.1.1⟩) (fun _ _ h => h)) inverse inverse (SharedR2.r2_ct K ct countFits)

end VG.Proof.Bignum.Arm
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem sharedPrepare_ct {base src : BitVec 32} {len k : Nat}
    {P : State → Prop} {regions : List Region}
    (K : TwoExp.Montgomery base len (Spec.Rsa.modulusWords k) P regions)
    (ct : TwoExp.MontgomeryTiming K) (countFits : 128 * Spec.Rsa.modulusWords k < 2 ^ 32) :
    RelCT isa (fun s t => (PrepareInput base src len k s ∧ P s) ∧
      (PrepareInput base src len k t ∧ P t) ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.SharedPrepare.code K.op) (fun _ _ => True) := by
  have ready (s : State) (h : PrepareInput base src len k s ∧ P s) :
      WP isa VG.Impl.Bignum.Arm.PublicFn.prepare s fun t =>
        PrecomputeInput base src len (Spec.Rsa.modulusWords k) k t ∧ P t :=
    WP.mono (prepare_input s h.1) fun _ r => ⟨r.1, K.stable r.2.1 r.2.2 h.2⟩
  unfold VG.Impl.Ffdh.Arm.SharedPrepare.code
  exact relCT_chain (prepareInput_ct.mono (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ h => h))
    ready ready (sharedPrecompute_ct K ct countFits)

end VG.Proof.Ffdh.Arm

end

end

/-! ### `Ffdh.Arm.SharedCheckPublicCorrect`, which only this module used -/

section

/-! The native callable public check satisfies the shared FFDH result contract. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem sharedCheckPublic_data (s : State) (pre : (Spec.Ffdh.checkPublicContract abi 176).pre s) :
    ∃ (p : Inputs) (yb : List Byte), stackArg s 1 = p.base ∧ s.gpr .r0 = p.domain ∧
      s.gpr .r3 = p.publicValue ∧ (s.gpr .r2).toNat = p.k ∧ (stackArg s 2).toNat = p.len ∧
      Spec.Rsa.bytesAt s.mem (State.addr p.domain) (s.gpr .r1).toNat = p.dom ∧
      Spec.Rsa.bytesAt s.mem (State.addr p.publicValue) p.k = yb ∧ SharedCheckPublicFnInput p yb s := by
  have original := pre
  sig_pre [Spec.Ffdh.checkPublicContract, Spec.Ffdh.checkPublicSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at pre
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, bounds, domainLen, yLen, space⟩ := pre
  let dom := Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat
  have domLength : dom.length = (s.gpr .r1).toNat := VG.Proof.Bignum.bytesAt_length _ _ _
  let p : Inputs := {
    base := stackArg s 1
    domain := s.gpr .r0
    publicValue := s.gpr .r3
    privateValue := 0
    output := 0
    entropy := 0
    len := (stackArg s 2).toNat
    k := (s.gpr .r2).toNat
    privateLength := 0
    hasQ := decide ((s.gpr .r1).toNat = 3 * (s.gpr .r2).toNat)
    dom := dom
    minLength := bounds.1
    maxLength := bounds.2
    space := space
    domainLength := by
      rw [domLength]
      simp only [decide_eq_true_eq]
      split
      · assumption
      · rcases domainLen with h | h
        · exact h
        · contradiction }
  let yb := Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r3)) (s.gpr .r2).toNat
  exact ⟨p, yb, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    sharedCheckPublic_input s original (p := p) (yb := yb) rfl rfl rfl rfl rfl rfl rfl⟩

theorem sharedCheckPublic_correct (b : MontBackend) (s : State) (pre : (Spec.Ffdh.checkPublicContract abi 176).pre s) :
    ∃ tr t, Exec isa (SharedCheckPublic.code b) s tr t ∧
      abiPreserved s t ∧ (Spec.Ffdh.checkPublicContract abi 176).post s t := by
  obtain ⟨p, yb, _, domain, value, count, _, domainBytes, valueBytes, input⟩ := sharedCheckPublic_data s pre
  obtain ⟨tr, t, run, preserved, result⟩ := sharedCheckPublicFn_ok b s input
  refine ⟨tr, t, run, preserved, ?_⟩
  have yLen : (stackArg s 0).toNat = (s.gpr .r2).toNat := by
    sig_pre [Spec.Ffdh.checkPublicContract, Spec.Ffdh.checkPublicSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at pre
    exact pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  sig_post [Spec.Ffdh.checkPublicContract, Spec.Ffdh.checkPublicSig, abi, argRegs, reduceClassify, Loc.val, State.addr]
  rw [BitVec.setWidth_append_eq_right]
  change Spec.Ffdh.domainValid (s.gpr .r2).toNat
    (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat) = true → _
  rw [domain, domainBytes, count]
  intro valid
  rw [yLen, count, value]
  change (t.gpr .r0).toNat = if Spec.Ffdh.publicValid
    ⟨Spec.Ffdh.domainOf p.k (Spec.Rsa.bytesAt s.mem (State.addr p.domain) (s.gpr .r1).toNat),
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr p.publicValue) p.k)⟩ then 1 else 0
  rw [domainBytes, valueBytes, result, checkedPublicFlag_spec p (Spec.Rsa.os2ip yb) valid]
  split <;> rfl

end VG.Proof.Ffdh.Arm

end

end

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

end VG.Proof.Ffdh.Arm.SharedCheckPublic
