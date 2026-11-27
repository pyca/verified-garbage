module

public import VerifiedGarbage.Proof.Ffdh.Arm.EntryStore
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
public import Init.Data.BitVec.BasicAux
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicBody
public import VerifiedGarbage.Proof.Ffdh.Arm.Frame
import VerifiedGarbage.Proof.Ffdh.Arm.Block
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
import VerifiedGarbage.Proof.Bignum.Arm.Stack
public import VerifiedGarbage.TCB.Arm.Isa
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicMain
import VerifiedGarbage.Proof.Ffdh.Arm.PrepareAtCT
import VerifiedGarbage.Proof.Ffdh.Arm.ImportAtCT
import VerifiedGarbage.Proof.Ffdh.Arm.Range
import VerifiedGarbage.Proof.Ffdh.Arm.RangeCT
import VerifiedGarbage.Proof.Ffdh.Arm.BranchCT
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Ffdh.Arm.Branch
import VerifiedGarbage.Proof.Ffdh.Arm.ImportAt
import VerifiedGarbage.Proof.Ffdh.Arm.QTest
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Ffdh.Arm.Subgroup
import VerifiedGarbage.Proof.Ffdh.Arm.ValueChecksCT
import VerifiedGarbage.Proof.Ffdh.Arm.PowerAtCT
public import VerifiedGarbage.Impl.Ffdh.Arm.PublicScan
public import VerifiedGarbage.Proof.Ffdh.Arm.Octets
import VerifiedGarbage.Proof.Ffdh.Arm.KeyScanCT
meta import VerifiedGarbage.Impl.Ffdh.Arm.PublicScan
meta import VerifiedGarbage.Proof.Framework.Arm.Taint

/-! ### `Ffdh.Arm.CheckPublicEntryCT`, which the modules that import this one used -/

section

/-! ### `Ffdh.Arm.SubgroupCT`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.PublicScanCT`, which this module and modules that import it used -/

section

/-! The public-prefix scan follows only the identical public exponent bytes. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.PublicScan
open VG VG.Arm VG.Proof.Ffdh.Arm VG.Proof.Bignum.Arm
open VG.Impl.Ffdh.Arm.PublicScan

structure Input (base src : BitVec 32) (len : Nat) (bs : List Byte) (s : State) : Prop where
  source : Octets base src len bs s
  pointer : s.gpr .r1 = src
  count : s.gpr .r2 = BitVec.ofNat 32 bs.length

theorem enter_ct : RelCT isa (fun _ _ => True) (.block enter) (fun _ _ => True) := by
  apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
  intro s t _; exact Taint.agree_ofRegs (by simp)

theorem leave_ct : RelCT isa (fun _ _ => True) (.block leave) (fun _ _ => True) := by
  apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
  intro s t _; exact Taint.agree_ofRegs (by simp)

private theorem enter_input (s : State) {base src : BitVec 32} {len : Nat} {bs : List Byte}
    (h : Input base src len bs s) :
    WP isa (.block enter) s (KeyScanState base src len bs) := by
  refine WP.mono (enter_ok s) ?_
  rintro t ⟨⟨ptr,count,_,_,mem⟩,rest⟩
  have frame : Frame [] s.mem t.mem := by rw [mem]; exact Frame.refl _ _
  exact ⟨h.source.after_frame frame rest (by simp),ptr.trans h.pointer,count.trans h.count⟩

theorem code_ct {base src : BitVec 32} {len : Nat} {bs : List Byte}
    (positive : 0 < bs.length) (fits : bs.length < 2^32) :
    RelCT isa (fun s t => Input base src len bs s ∧ Input base src len bs t ∧ s.sp = t.sp)
      code (fun _ _ => True) := by
  unfold code
  have scan : RelCT isa
      (fun s t => KeyScanState base src len bs s ∧ KeyScanState base src len bs t ∧ s.sp = t.sp)
      scan (fun _ _ => True) := keyScan_ct positive fits
  exact relCT_chain
    (enter_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h))
    (fun s h => enter_input s h) (fun s h => enter_input s h)
    (scan.seq leave_ct)

end VG.Proof.Ffdh.Arm.PublicScan

end

end

/-! Subgroup checks have a trace determined by the domain width and pointers. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/PublicPowerAtCT.lean`, which only this module imported.
section

/-! Public subgroup exponentiation skips only identical public zero prefixes. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt)

theorem publicPowerAt_ct {p : Inputs} {slots : List Nat} {bs es ec M : Nat} {bb eb : List Byte}
    (stable : stableSlots slots = true) (hb : bs ∈ slots) (he : es ∈ slots) (hc : ec ∈ slots) (hk : 32 ∈ slots)
    (baseLength : bb.length = p.k) (positive : 0 < eb.length) (fits : eb.length < 2 ^ 32)
    (count : p.slotValue ec = BitVec.ofNat 32 eb.length) (odd : M % 2 = 1) :
    RelCT isa (fun s t => PowerAtInput p slots bs es M bb eb s ∧
      PowerAtInput p slots bs es M bb eb t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.Domain.publicPowerAt bs es ec) (fun _ _ => True) := by
  have leadLt := VG.Proof.Ffdh.lead_lt (bs := eb) (by intro empty; rw [empty] at positive; simp at positive)
  have trimmedPositive : 0 < (eb.drop (VG.Proof.Ffdh.lead eb)).length := by
    simp only [List.length_drop]; omega
  have tableFit : Proof.Rsa.Mont.arrAt p.w 3 + 32 ≤ 8*p.len := by
    have fit := p.width.2.2.1
    simp only [Proof.Rsa.Mont.arrAt,Proof.Rsa.Mont.hdrBytes] at *
    omega
  have scan := (PublicScan.code_ct positive fits).mono
    (P' := fun (s t : State) => PowerInput p.base (p.slotValue bs) (p.slotValue es) p.len p.w M bb eb s ∧
      PowerInput p.base (p.slotValue bs) (p.slotValue es) p.len p.w M bb eb t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨⟨h.1.exponentBytes,h.1.exponent,h.1.exponentCount⟩,
      ⟨h.2.1.exponentBytes,h.2.1.exponent,h.2.1.exponentCount⟩,h.2.2⟩) (fun _ _ h => h)
  have tail := relCT_chain scan
    (fun s h => WP.mono (PublicScan.input_ok s h) fun _ k => k.1)
    (fun s h => WP.mono (PublicScan.input_ok s h) fun _ k => k.1)
    (power_ct tableFit p.width.2.2.1 trimmedPositive rfl rfl)
  unfold VG.Impl.Ffdh.Arm.Domain.publicPowerAt
  exact relCT_chain
    ((powerArgs_ct bs es ec).mono (fun _ _ h => h.2.2) (fun _ _ _ => trivial))
    (fun s h => powerArgs_input s stable hb he hc hk baseLength positive fits count odd h)
    (fun s h => powerArgs_input s stable hb he hc hk baseLength positive fits count odd h) tail

end VG.Proof.Ffdh.Arm
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (Operand)

structure SubgroupInput (p : Inputs) (slots : List Nat) (slot : Nat) (bb : List Byte) (s : State) : Prop where
  context : Context p slots s
  ready : ArithmeticReady p.base p.len p.w s
  modulus : Proof.Rsa.Mont.numAt s.mem (State.addr p.base) p.w 0 = p.P
  r2 : Proof.Rsa.Mont.numAt s.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P
  source : Octets p.base (p.slotValue slot) p.len bb s

theorem SubgroupInput.after_workspace {p : Inputs} {slots : List Nat} {slot : Nat} {bb : List Byte}
    {s t : State} {rs : List Reg} (h : SubgroupInput p slots slot bb s)
    (stable : stableSlots slots = true) (frame : Frame [⟨State.addr p.base, 8 * p.len⟩] s.mem t.mem)
    (rest : VG.Proof.X25519.Arm.Rest rs s t) (ready : ArithmeticReady p.base p.len p.w t)
    (modulus : Proof.Rsa.Mont.numAt t.mem (State.addr p.base) p.w 0 = p.P)
    (r2 : Proof.Rsa.Mont.numAt t.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P) :
    SubgroupInput p slots slot bb t :=
  ⟨h.context.after_workspace frame rest ready.ptr (fun d hd => (stableSlots_at (d := d) stable hd).1),
    ready, modulus, r2, h.source.after_workspace frame rest⟩

theorem SubgroupInput.after_mem {p : Inputs} {slots : List Nat} {slot : Nat} {bb : List Byte}
    {s t : State} {rs : List Reg} (h : SubgroupInput p slots slot bb s)
    (stable : stableSlots slots = true) (mem : t.mem = s.mem) (rest : VG.Proof.X25519.Arm.Rest rs s t)
    (ptr : t.gpr .r0 = p.base) : SubgroupInput p slots slot bb t := by
  have frame : Frame [⟨State.addr p.base, 8 * p.len⟩] s.mem t.mem := by rw [mem]; exact Frame.refl _ _
  exact ⟨h.context.after_workspace frame rest ptr (fun d hd => (stableSlots_at (d := d) stable hd).1),
    h.ready.of_mem mem rest ptr, by rw [mem]; exact h.modulus,
    by rw [mem]; exact h.r2, h.source.after_workspace frame rest⟩

theorem subgroup_ct {p : Inputs} {slots : List Nat} {slot : Nat} {bb : List Byte}
    (stable : stableSlots slots = true) (hb : slot ∈ slots) (h60 : 60 ∈ slots) (h32 : 32 ∈ slots)
    (hasQ : p.hasQ = true) (baseLength : bb.length = p.k) (odd : p.P % 2 = 1) :
    RelCT isa (fun s t => SubgroupInput p slots slot bb s ∧ SubgroupInput p slots slot bb t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.Domain.subgroup slot) (fun _ _ => True) := by
  have positive : 0 < ((p.dom.drop (2 * p.k)).take p.k).length := by
    rw [p.qLength hasQ]; have := p.minLength; omega_using [this]
  have fits : ((p.dom.drop (2 * p.k)).take p.k).length < 2 ^ 32 := by
    rw [p.qLength hasQ]; have := p.maxLength; omega_using [this]
  have count : p.slotValue 32 = BitVec.ofNat 32 ((p.dom.drop (2 * p.k)).take p.k).length := by
    change BitVec.ofNat 32 p.k = _; rw [p.qLength hasQ]
  have powers := (publicPowerAt_ct (p := p) (bs := slot) (es := 60) (ec := 32)
    stable hb h60 h32 h32 baseLength positive fits count odd).mono
    (P' := fun (s t : State) => SubgroupInput p slots slot bb s ∧ SubgroupInput p slots slot bb t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨⟨h.1.context, h.1.ready, h.1.modulus, h.1.r2, h.1.source, h.1.context.qBytes hasQ⟩,
      ⟨h.2.1.context, h.2.1.ready, h.2.1.modulus, h.2.1.r2, h.2.1.source, h.2.1.context.qBytes hasQ⟩, h.2.2⟩)
    (fun _ _ h => h)
  have wp (s : State) (h : SubgroupInput p slots slot bb s) :=
    WP.mono (publicPowerAt_ok s slot 60 32 h.context stable hb h60 h32 h32 h.ready h.modulus odd h.r2
      h.source baseLength (h.context.qBytes hasQ) positive fits count) fun _ j => j.2.1
  unfold VG.Impl.Ffdh.Arm.Domain.subgroup
  exact relCT_chain powers wp wp (isOne_ct (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp] : Operand 6))

end VG.Proof.Ffdh.Arm

end

end

/-! ### `Ffdh.Arm.CheckPublicMainCT`, which the modules that import this one used -/

section

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
    h.context.domainStack.sub_left (Region.sub_prefix (by rw [p.domainLength]; split <;> omega_using []))
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
      (by rw [length]; have := p.minLength; omega_using [this]) (by rw [length]; exact p.width.2.2.2.1)
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

end

end

/-! The public-check entry accesses only fixed local and incoming stack slots. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

theorem checkPublicEntry_ct : RelCT isa (fun s t => s.sp = t.sp)
    (.block VG.Impl.Ffdh.Arm.Domain.CheckPublic.entry) (fun s t => s.sp = t.sp) := by
  have stores := RelCT.block_append ((storeLocal_ct .r0 24).seq
    (RelCT.block_append ((storeLocal_ct .r1 28).seq
    (RelCT.block_append ((storeLocal_ct .r2 32).seq
    (RelCT.block_append ((storeLocal_ct .r3 36).seq
    (RelCT.block_append ((loadLocal_ct .r0 132 (by decide)).seq (storeLocal_ct .r0 0))))))))))
  exact (RelCT.block_append (stackAddr_ct.seq stores)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)

end VG.Proof.Ffdh.Arm

end

end

/-! ### `Ffdh.Arm.CheckPublicFn`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.CheckPublicEntry`, which this module and modules that import it used -/

section

/-! The imported-public-value ABI arguments are retained in native locals. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

structure PublicEntryRegs (p : Inputs) (s : State) : Prop where
  domain : s.gpr .r0 = p.domain
  domainLength : s.gpr .r1 = BitVec.ofNat 32 p.dom.length
  count : s.gpr .r2 = BitVec.ofNat 32 p.k
  publicValue : s.gpr .r3 = p.publicValue
  stackBase : s.gpr .r12 = s.sp

theorem PublicEntryRegs.after {p : Inputs} {s t : State}
    (h : PublicEntryRegs p s) (rest : Rest [] s t) : PublicEntryRegs p t :=
  ⟨(rest.gpr .r0 (by simp)).trans h.domain, (rest.gpr .r1 (by simp)).trans h.domainLength,
    (rest.gpr .r2 (by simp)).trans h.count, (rest.gpr .r3 (by simp)).trans h.publicValue,
    (rest.gpr .r12 (by simp)).trans (h.stackBase.trans rest.sp.symm)⟩

theorem checkPublicEntry_ok (s : State) {p : Inputs}
    (h : ArgumentMemory p [] s) (incoming : IncomingScratch p s)
    (domain : s.gpr .r0 = p.domain) (domainLength : s.gpr .r1 = BitVec.ofNat 32 p.dom.length)
    (count : s.gpr .r2 = BitVec.ofNat 32 p.k) (publicValue : s.gpr .r3 = p.publicValue) :
    WP isa (.block VG.Impl.Ffdh.Arm.Domain.CheckPublic.entry) s fun t =>
      Context p [0, 36, 32, 28, 24] t ∧ Frame [⟨State.addr s.sp, 72⟩] s.mem t.mem := by
  unfold VG.Impl.Ffdh.Arm.Domain.CheckPublic.entry VG.Impl.Ffdh.Arm.Domain.st
  refine wp_stackAddr (by decide) fun u moved => ?_
  have restU : Rest [.r12] s u := moved.rest (by simp)
  have argsU := h.of_mem moved.mem restU
  have frameU : Frame [⟨State.addr s.sp, 72⟩] s.mem u.mem := by rw [moved.mem]; exact Frame.refl _ _
  have incomingU := incoming.after frameU restU
  have regsU : PublicEntryRegs p u :=
    ⟨(moved.other .r0 (by decide)).trans domain, (moved.other .r1 (by decide)).trans domainLength,
      (moved.other .r2 (by decide)).trans count, (moved.other .r3 (by decide)).trans publicValue,
      by rw [moved.gpr, moved.sp, BitVec.add_zero]⟩
  refine wp_store_arg .r0 24 argsU (by decide) (by decide) (by decide) regsU.domain regsU.stackBase fun v argsV frameV restV => ?_
  have regsV := regsU.after restV
  have incomingV := incomingU.after frameV restV
  rw [restU.sp] at frameV
  have fullV := frameU.trans frameV
  refine wp_store_arg .r1 28 argsV (by decide) (by decide) (by decide) regsV.domainLength regsV.stackBase fun w argsW frameW restW => ?_
  have regsW := regsV.after restW
  have incomingW := incomingV.after frameW restW
  rw [restV.sp, restU.sp] at frameW
  have fullW := fullV.trans frameW
  refine wp_store_arg .r2 32 argsW (by decide) (by decide) (by decide) regsW.count regsW.stackBase fun x argsX frameX restX => ?_
  have regsX := regsW.after restX
  have incomingX := incomingW.after frameX restX
  rw [restW.sp, restV.sp, restU.sp] at frameX
  have fullX := fullW.trans frameX
  refine wp_store_arg .r3 36 argsX (by decide) (by decide) (by decide) regsX.publicValue regsX.stackBase fun y argsY frameY restY => ?_
  have regsY := regsX.after restY
  have incomingY := incomingX.after frameY restY
  rw [restX.sp, restW.sp, restV.sp, restU.sp] at frameY
  have fullY := fullX.trans frameY
  refine wp_loadStack (a := off (State.addr y.sp) 132) (by decide)
    (addr_add (by have := incomingY.fits; omega_using [this])) incomingY.readable fun z loaded => ?_
  have restZ : Rest [.r0] y z := loaded.rest (by simp)
  have argsZ := argsY.of_mem loaded.mem restZ
  have baseZ : z.gpr .r0 = p.base := loaded.gpr.trans incomingY.value
  have spZ : z.gpr .r12 = z.sp := (loaded.other .r12 (by decide)).trans (regsY.stackBase.trans loaded.sp.symm)
  refine wp_store_arg .r0 0 argsZ (by decide) (by decide) (by decide) baseZ spZ fun t argsT frameT restT => WP.block_nil ?_
  refine ⟨⟨argsT, (restT.gpr .r0 (by simp)).trans baseZ⟩, ?_⟩
  rw [restZ.sp, restY.sp, restX.sp, restW.sp, restV.sp, restU.sp] at frameT
  rw [loaded.mem] at frameT
  exact fullY.trans frameT

end VG.Proof.Ffdh.Arm

end

end

/-! The native public-value check, from its entry through AAPCS restoration. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont

theorem checkPublicEntered_ok (s : State) {p : Inputs} {yb : List Byte}
    (h : ArgumentMemory p [] s) (incoming : IncomingScratch p s)
    (domain : s.gpr .r0 = p.domain) (domainLength : s.gpr .r1 = BitVec.ofNat 32 p.dom.length)
    (count : s.gpr .r2 = BitVec.ofNat 32 p.k) (publicValue : s.gpr .r3 = p.publicValue)
    (value : Octets p.base p.publicValue p.len yb s) (length : yb.length = p.k)
    (valueStack : Region.Disjoint ⟨State.addr p.publicValue, yb.length⟩ ⟨State.addr s.sp, 72⟩) :
    WP isa (.seq (.block VG.Impl.Ffdh.Arm.Domain.CheckPublic.entry)
      (VG.Impl.Ffdh.Arm.Domain.head VG.Impl.Ffdh.Arm.Domain.CheckPublic.main)) s fun t =>
      t.gpr .r0 = checkedPublicFlag p (Spec.Rsa.os2ip yb) ∧ Frame (bodyWrites p s) s.mem t.mem := by
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
  refine WP.mono (checkPublicBody_ok u contextU (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) valueU length valueStackU) ?_
  rintro t ⟨result, frameT⟩
  refine ⟨result, ?_⟩
  have entryFrame : Frame (bodyWrites p s) s.mem u.mem := frameU.mono (by simp [bodyWrites])
  change Frame [⟨State.addr p.base, 8 * p.len⟩, ⟨State.addr u.sp, 72⟩] u.mem t.mem at frameT
  rw [restU.sp] at frameT
  exact entryFrame.trans frameT

structure CheckPublicFnInput (p : Inputs) (yb : List Byte) (s : State) : Prop where
  stackFits : 128 ≤ s.sp.toNat
  args : ArgumentMemory p [] (entered s)
  incoming : IncomingScratch p (entered s)
  domain : s.gpr .r0 = p.domain
  domainLength : s.gpr .r1 = BitVec.ofNat 32 p.dom.length
  count : s.gpr .r2 = BitVec.ofNat 32 p.k
  publicValue : s.gpr .r3 = p.publicValue
  value : Octets p.base p.publicValue p.len yb (entered s)
  length : yb.length = p.k
  valueStack : Region.Disjoint ⟨State.addr p.publicValue, yb.length⟩ ⟨State.addr (entered s).sp, 72⟩
  saved : ∀ r ∈ bodyWrites p (entered s), (⟨State.addr (pcPushed s).sp, 56⟩ : Region).Disjoint r

theorem checkPublicFn_ok (s : State) {p : Inputs} {yb : List Byte} (h : CheckPublicFnInput p yb s) :
    WP isa VG.Impl.Ffdh.Arm.Domain.CheckPublic.code s fun t =>
      abiPreserved s t ∧ t.gpr .r0 = checkedPublicFlag p (Spec.Rsa.os2ip yb) := by
  unfold VG.Impl.Ffdh.Arm.Domain.CheckPublic.code
  refine framed_of_separate _ s h.stackFits (bodyWrites p (entered s))
    (fun _ status => status = checkedPublicFlag p (Spec.Rsa.os2ip yb)) h.saved ?_
  refine WP.mono (checkPublicEntered_ok (entered s) h.args h.incoming h.domain h.domainLength
    h.count h.publicValue h.value h.length h.valueStack) ?_
  rintro t ⟨result, frame⟩
  exact ⟨frame, result⟩

end VG.Proof.Ffdh.Arm

end

end

/-! The shared signature supplies the native public-check frame and buffers. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont

theorem checkPublic_input (s : State) (pre : (Spec.Ffdh.checkPublicContract abi 128).pre s)
    {p : Inputs} {yb : List Byte}
    (base : stackArg s 1 = p.base) (domain : s.gpr .r0 = p.domain) (publicValue : s.gpr .r3 = p.publicValue)
    (count : (s.gpr .r2).toNat = p.k) (capacity : (stackArg s 2).toNat = p.len)
    (domainBytes : Spec.Rsa.bytesAt s.mem (State.addr p.domain) (s.gpr .r1).toNat = p.dom)
    (publicBytes : Spec.Rsa.bytesAt s.mem (State.addr p.publicValue) p.k = yb) :
    CheckPublicFnInput p yb s := by
  sig_pre [Spec.Ffdh.checkPublicContract, Spec.Ffdh.checkPublicSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at pre
  obtain ⟨stackFit, argFit, rd, wr, domS, yS, sArgs, stackDom, stackY, stackS, stackArgs,
    domFit, yFit, sFit, _, _, yLen, _⟩ := pre
  have domLen : (s.gpr .r1).toNat = p.dom.length := by
    have eq := congrArg List.length domainBytes
    simpa only [VG.Proof.Bignum.bytesAt_length] using eq
  have length : yb.length = p.k := by
    have eq := congrArg List.length publicBytes
    simpa only [VG.Proof.Bignum.bytesAt_length] using eq.symm
  rw [yLen, count] at rd yS stackY yFit
  rw [domain] at rd domS stackDom domFit
  rw [publicValue] at rd yS stackY yFit
  rw [base, capacity, Nat.mul_comm p.len 8] at wr domS yS sArgs stackS sFit
  rw [domLen] at rd domS stackDom domFit
  have reserved : State.addr s.sp - BitVec.ofNat 64 128 = State.addr (s.sp - BitVec.ofNat 32 128) :=
    (FrameStack.addr_sub' stackFit).symm
  simp only [State.addr] at reserved
  rw [reserved] at stackDom stackY stackS stackArgs
  have ws : Workspace s p.base (8 * p.len) := ⟨sFit, by rw [wr]; simp [State.addr]⟩
  have domRead : InRegions (s.rd ++ s.wr) (State.addr p.domain) p.dom.length :=
    ⟨⟨State.addr p.domain, p.dom.length⟩, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
  have valueRead : InRegions (s.rd ++ s.wr) (State.addr p.publicValue) p.k :=
    ⟨⟨State.addr p.publicValue, p.k⟩, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
  have domOctets : Octets p.base p.domain p.len p.dom s :=
    ⟨domFit, domRead, domS, by rw [← domLen]; exact domainBytes⟩
  have valueOctets : Octets p.base p.publicValue p.len yb s :=
    ⟨by rw [length]; exact yFit, by rw [length]; exact valueRead,
      by rw [length]; exact yS, by rw [length]; exact publicBytes⟩
  have locals := entered_locals s stackFit stackS
  have domEntered := entered_octets domOctets stackFit stackDom
  have valueEntered := entered_octets valueOctets stackFit (by rw [length]; exact stackY)
  have args : ArgumentMemory p [] (entered s) :=
    ⟨entered_workspace ws, locals, domEntered,
      stackDom.symm.sub_right (locals_sub_reserved s stackFit), by simp⟩
  have argAddr : stackArgAddr s 1 = off (State.addr s.sp) 4 := VG.Arm.addr_add (by omega_using [argFit])
  have argStart : stackArgAddr s 0 = State.addr s.sp := by simp [stackArgAddr]
  have contains : (⟨stackArgAddr s 0, 12⟩ : Region).Contains (stackArgAddr s 1) 4 := by
    rw [argStart, argAddr]
    exact Offset.contains_base _ (by decide) (by decide)
  have argRead : InRegions (s.rd ++ s.wr) (stackArgAddr s 1) 4 :=
    ⟨⟨stackArgAddr s 0, 12⟩, List.mem_append_left _ (by rw [rd]; simp), contains⟩
  have nativeRoom : (entered s).sp.toNat + 132 < 2 ^ 32 := by rw [entered_nat s stackFit]; omega_using [argFit]
  have nativeAddr : off (State.addr (entered s).sp) 132 = stackArgAddr s 1 := by
    change State.addr (entered s).sp + BitVec.ofNat 64 132 = _
    rw [← VG.Arm.addr_add nativeRoom, entered_sp]
    have split : BitVec.ofNat 32 132 = BitVec.ofNat 32 128 + BitVec.ofNat 32 4 := rfl
    rw [split, ← BitVec.add_assoc, BitVec.sub_add_cancel]
    rfl
  have incoming : IncomingScratch p (entered s) := by
    refine ⟨by rw [entered_nat s stackFit]; omega_using [argFit], ?_, ?_⟩
    · rw [nativeAddr]; exact entered_read argRead
    · rw [nativeAddr]
      have word := (entered_frame s stackFit).readW (w := 32) contains (by
        intro r hr
        rw [List.mem_singleton] at hr
        subst r
        exact stackArgs.symm.sub_right (saved_sub_reserved s stackFit)) (by decide)
      rw [word]
      exact base
  refine ⟨stackFit, args, incoming, domain, ?_, ?_, publicValue, valueEntered, length, ?_, ?_⟩
  · rw [← domLen, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [← count, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [length]
    exact stackY.symm.sub_right (locals_sub_reserved s stackFit)
  · intro r hr
    simp only [bodyWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact stackS.sub_left (saved_sub_reserved s stackFit)
    · exact saved_separate_locals s stackFit

end VG.Proof.Ffdh.Arm
