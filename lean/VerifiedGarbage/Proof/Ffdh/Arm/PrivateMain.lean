module

public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
import VerifiedGarbage.Proof.Ffdh.Arm.PowerAt
import VerifiedGarbage.Proof.Ffdh.Arm.ImportAt
import VerifiedGarbage.Proof.Ffdh.Arm.Equal
import VerifiedGarbage.Proof.Ffdh.Arm.Branch
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Impl.Ffdh.Arm.Checks
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
import VerifiedGarbage.Proof.Ffdh.Arm.Subgroup
import VerifiedGarbage.Proof.Ffdh.Arm.QTest
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Ffdh.Arm.Range
import VerifiedGarbage.Proof.Ffdh.Arm.ScalarRange
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareAt
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ffdh.Arm.ScalarUpper

/-! ### `Ffdh.Arm.PrivatePublic`, which only this module used -/

section

/-! ### `Ffdh.Arm.PrivateTail`, which only this module used -/

section

/-! ### `Ffdh.Arm.PrivateMatch`, which only this module used -/

section

/-! Imported key consistency is checked by native exponentiation and full-width equality. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt Operand arrAt)

def privateMatchFlag (p : Inputs) (yb xb : List Byte) : BitVec 32 :=
  if Spec.Rsa.powMod p.G (Spec.Rsa.os2ip xb) p.P = Spec.Rsa.os2ip yb then 1 else 0

theorem privateMatch_ok (s : State) {p : Inputs} {slots : List Nat} {yb xb : List Byte}
    (h : Context p slots s) (stable : stableSlots slots = true)
    (h32 : 32 ∈ slots) (h36 : 36 ∈ slots) (h40 : 40 ∈ slots) (h44 : 44 ∈ slots) (h56 : 56 ∈ slots)
    (ready : ArithmeticReady p.base p.len p.w s)
    (modulus : numAt s.mem (State.addr p.base) p.w 0 = p.P) (odd : p.P % 2 = 1)
    (r2 : numAt s.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P)
    (value : Octets p.base p.publicValue p.len yb s) (length : yb.length = p.k)
    (scalar : Octets p.base p.privateValue p.len xb s) (positive : 0 < xb.length) (fits : xb.length < 2 ^ 32)
    (count : p.slotValue 44 = BitVec.ofNat 32 xb.length) :
    WP isa VG.Impl.Ffdh.Arm.Domain.CheckPrivate.matchPublic s fun t =>
      t.gpr .r0 = privateMatchFlag p yb xb ∧ Frame [⟨State.addr p.base, 8 * p.len⟩] s.mem t.mem := by
  have op1 : Operand 1 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op6 : Operand 6 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  rw [VG.Impl.Ffdh.Arm.Domain.CheckPrivate.matchPublic, WP.seq_iff]
  refine WP.mono (powerAt_ok s 56 40 44 h stable h56 h40 h44 h32 ready modulus odd r2
    h.gBytes p.gLength scalar positive fits count) ?_
  rintro u ⟨contextU, readyU, power, _, _, _, frameU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (importAt_ok u 1 36 32 contextU stable h36 h32 readyU (by decide) (by decide)
    (value.after_workspace frameU restU) (by rw [length]; have := p.minLength; omega_using [this])
    (by rw [length]; exact p.width.2.2.2.1) (by change BitVec.ofNat 32 p.k = _; rw [length])) ?_
  rintro v ⟨_, readyV, y, keepsV, frameV, _⟩
  have fit : arrAt p.w 8 ≤ 8 * p.len := readyV.width ▸ readyV.layout.2.2.1
  have powerV := (keeps_array_num keepsV fit op6 (by decide)).trans power
  rw [WP.seq_iff]
  refine WP.mono (equal_ok v readyV op6 op1) ?_
  rintro w ⟨_, flag, _, frameW, _⟩
  rw [powerV, y] at flag
  refine WP.mono (finishFlag_ok w) ?_
  rintro t ⟨⟨result, memT⟩, _⟩
  exact ⟨by rw [result, flag]; rfl, by rw [memT]; exact (frameU.trans frameV).trans frameW⟩

end VG.Proof.Ffdh.Arm

end

end


/-! Imported public subgroup membership precedes native private-key consistency checking. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)

def privateTailFlag (p : Inputs) (yb xb : List Byte) : BitVec 32 :=
  if p.hasQ = true then
    if Spec.Rsa.powMod (Spec.Rsa.os2ip yb) p.Q p.P = 1 then privateMatchFlag p yb xb else 0
  else privateMatchFlag p yb xb

theorem privateTail_ok (s : State) {p : Inputs} {slots : List Nat} {yb xb : List Byte}
    (h : Context p slots s) (stable : stableSlots slots = true)
    (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) (h36 : 36 ∈ slots) (h40 : 40 ∈ slots)
    (h44 : 44 ∈ slots) (h56 : 56 ∈ slots) (h60 : 60 ∈ slots)
    (ready : ArithmeticReady p.base p.len p.w s)
    (modulus : numAt s.mem (State.addr p.base) p.w 0 = p.P) (odd : p.P % 2 = 1)
    (r2 : numAt s.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P)
    (value : Octets p.base p.publicValue p.len yb s) (length : yb.length = p.k)
    (scalar : Octets p.base p.privateValue p.len xb s) (positive : 0 < xb.length) (fits : xb.length < 2 ^ 32)
    (count : p.slotValue 44 = BitVec.ofNat 32 xb.length) :
    WP isa VG.Impl.Ffdh.Arm.Domain.CheckPrivate.tail s fun t =>
      t.gpr .r0 = privateTailFlag p yb xb ∧ Frame [⟨State.addr p.base, 8 * p.len⟩] s.mem t.mem := by
  rw [VG.Impl.Ffdh.Arm.Domain.CheckPrivate.tail, VG.Impl.Ffdh.Arm.Domain.withQ, WP.seq_iff]
  refine WP.mono (qTest_ok s h h28 h32) ?_
  rintro u ⟨⟨zero, memU⟩, restU⟩
  have ptrU := (restU.gpr .r0 (by simp)).trans h.ptr
  have contextU := h.of_mem memU restU ptrU
  have readyU := ready.of_mem memU restU ptrU
  have frameU : Frame [⟨State.addr p.base, 8 * p.len⟩] s.mem u.mem := by rw [memU]; exact Frame.refl _ _
  have valueU := value.after_workspace frameU restU
  have scalarU := scalar.after_workspace frameU restU
  refine WP.ite p.hasQ (by simp only [eval, zero, Bool.not_not]) ?_ ?_
  · intro hasQ
    rw [WP.seq_iff]
    refine WP.mono (subgroup_ok u 36 contextU stable h36 h60 h32 hasQ readyU
      (by rw [memU]; exact modulus) odd (by rw [memU]; exact r2) valueU length) ?_
    rintro v ⟨contextV, readyV, memberFlag, modV, r2V, frameV, restV⟩
    rw [VG.Impl.Ffdh.Arm.Domain.ifFlag, WP.seq_iff]
    refine WP.mono (testFlag_ok v) ?_
    rintro w ⟨⟨zeroW, memW⟩, restW⟩
    by_cases member : Spec.Rsa.powMod (Spec.Rsa.os2ip yb) p.Q p.P = 1
    · refine WP.ite true (by change some (!w.z) = some true; rw [zeroW, memberFlag, ite_eq_left member]; rfl) ?_ (by intro hf; cases hf)
      intro _
      have ptrW := (restW.gpr .r0 (by simp)).trans contextV.ptr
      have contextW := contextV.of_mem memW restW ptrW
      have readyW := readyV.of_mem memW restW ptrW
      have frameW : Frame [⟨State.addr p.base, 8 * p.len⟩] v.mem w.mem := by rw [memW]; exact Frame.refl _ _
      refine WP.mono (privateMatch_ok w contextW stable h32 h36 h40 h44 h56 readyW
        (by rw [memW]; exact modV) odd (by rw [memW]; exact r2V)
        ((valueU.after_workspace frameV restV).after_workspace frameW restW) length
        ((scalarU.after_workspace frameV restV).after_workspace frameW restW) positive fits count) ?_
      rintro t ⟨result, frameT⟩
      exact ⟨by rw [privateTailFlag, ite_eq_left hasQ, ite_eq_left member]; exact result,
        ((frameU.trans frameV).trans frameW).trans frameT⟩
    · refine WP.ite false (by change some (!w.z) = some false; rw [zeroW, memberFlag, ite_eq_right member]; rfl) (by intro ht; cases ht) ?_
      intro _
      refine WP.mono (ret_ok w 0 (by decide)) ?_
      rintro t ⟨⟨result, memT⟩, _⟩
      exact ⟨by rw [result, privateTailFlag, ite_eq_left hasQ, ite_eq_right member], by rw [memT, memW]; exact frameU.trans frameV⟩
  · intro hasQ
    refine WP.mono (privateMatch_ok u contextU stable h32 h36 h40 h44 h56 readyU
      (by rw [memU]; exact modulus) odd (by rw [memU]; exact r2) valueU length scalarU positive fits count) ?_
    rintro t ⟨result, frameT⟩
    exact ⟨by rw [privateTailFlag, ite_eq_right (by rw [hasQ]; decide)]; exact result, frameU.trans frameT⟩

end VG.Proof.Ffdh.Arm

end

end


/-! Native public-value range, subgroup, and private-key consistency checks. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt Operand arrAt)

def privatePublicFlag (p : Inputs) (yb xb : List Byte) : BitVec 32 :=
  if 1 < Spec.Rsa.os2ip yb ∧ Spec.Rsa.os2ip yb < p.P - 1 then privateTailFlag p yb xb else 0

theorem privatePublic_ok (s : State) {p : Inputs} {slots : List Nat} {yb xb : List Byte}
    (h : Context p slots s) (stable : stableSlots slots = true)
    (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) (h36 : 36 ∈ slots) (h40 : 40 ∈ slots)
    (h44 : 44 ∈ slots) (h56 : 56 ∈ slots) (h60 : 60 ∈ slots)
    (ready : ArithmeticReady p.base p.len p.w s)
    (modulus : numAt s.mem (State.addr p.base) p.w 0 = p.P) (odd : p.P % 2 = 1)
    (r2 : numAt s.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P)
    (value : Octets p.base p.publicValue p.len yb s) (length : yb.length = p.k)
    (scalar : Octets p.base p.privateValue p.len xb s) (positive : 0 < xb.length) (fits : xb.length < 2 ^ 32)
    (count : p.slotValue 44 = BitVec.ofNat 32 xb.length) :
    WP isa VG.Impl.Ffdh.Arm.Domain.CheckPrivate.publicCheck s fun t =>
      t.gpr .r0 = privatePublicFlag p yb xb ∧ Frame [⟨State.addr p.base, 8 * p.len⟩] s.mem t.mem := by
  have op0 : Operand 0 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op1 : Operand 1 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have extend {m m' : Mem} (f : Frame [⟨State.addr p.base, 8 * p.len⟩] m m') :
      Frame [⟨State.addr p.base, 8 * p.len⟩] m m' := f
  unfold VG.Impl.Ffdh.Arm.Domain.CheckPrivate.publicCheck
  rw [WP.seq_iff]
  refine WP.mono (importAt_ok s 1 36 32 h stable h36 h32 ready (by decide) (by decide)
    value (by rw [length]; have := p.minLength; omega_using [this]) (by rw [length]; exact p.width.2.2.2.1)
    (by change BitVec.ofNat 32 p.k = _; rw [length])) ?_
  rintro v ⟨contextV, readyV, y, keepsV, frameV, restV⟩
  have bound : arrAt p.w 8 ≤ 8 * p.len := readyV.width ▸ readyV.layout.2.2.1
  have modV := (keeps_array_num keepsV bound op0 (by decide : 0 ≠ 1)).trans modulus
  have r2V := (keeps_array_num keepsV bound op4 (by decide : 4 ≠ 1)).trans r2
  rw [WP.seq_iff]
  refine WP.mono (inRange_ok v readyV op1 (by decide) (by rw [modV]; exact odd)) ?_
  rintro w ⟨readyW, flag, arraysW, frameW, restW⟩
  rw [y, modV] at flag
  change w.gpr .r11 = (if 1 < Spec.Rsa.os2ip yb ∧ Spec.Rsa.os2ip yb < p.P - 1 then 1 else 0) at flag
  have contextW := contextV.after_workspace frameW restW readyW.ptr (fun d hd => (stableSlots_at stable hd).1)
  have modW := (arraysW 0 op0 (by decide)).trans modV
  have r2W := (arraysW 4 op4 (by decide)).trans r2V
  have valueW := (value.after_workspace frameV restV).after_workspace frameW restW
  have scalarW := (scalar.after_workspace frameV restV).after_workspace frameW restW
  have frameW' := ((Frame.refl _ _).trans (extend frameV)).trans (extend frameW)
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
    refine WP.mono (privateTail_ok z contextZ stable h28 h32 h36 h40 h44 h56 h60 readyZ
      (by rw [memZ]; exact modW) odd (by rw [memZ]; exact r2W)
      (valueW.after_workspace frameZ restZ) length (scalarW.after_workspace frameZ restZ) positive fits count) ?_
    rintro t ⟨result, frameT⟩
    refine ⟨?_, ?_⟩
    · rw [privatePublicFlag, ite_eq_left valid]; exact result
    · rw [memZ] at frameT
      exact frameW'.trans (extend frameT)
  · refine WP.ite false (by change some (!z.z) = some false; rw [zero, flag, ite_eq_right valid]; rfl) (by intro ht; cases ht) ?_
    intro _
    refine WP.mono (ret_ok z 0 (by decide)) ?_
    rintro t ⟨⟨result, memT⟩, _⟩
    refine ⟨?_, ?_⟩
    · rw [privatePublicFlag, ite_eq_right valid]; exact result
    · rw [memT, memZ]; exact frameW'

end VG.Proof.Ffdh.Arm

end

end


/-! Imported private-key validation keeps scalar validity and public-key consistency in native code. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt Operand arrAt)

def privateMainFlag (p : Inputs) (yb xb : List Byte) : BitVec 32 :=
  if 0 < Spec.Rsa.os2ip xb ∧ Spec.Rsa.os2ip xb < scalarBound p then privatePublicFlag p yb xb else 2

theorem privateMain_ok (s : State) {p : Inputs} {slots : List Nat} {yb xb : List Byte}
    (h : Context p slots s) (stable : stableSlots slots = true)
    (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots)
    (h36 : 36 ∈ slots) (h40 : 40 ∈ slots) (h44 : 44 ∈ slots) (h56 : 56 ∈ slots) (h60 : 60 ∈ slots)
    (large : 1 < p.P) (odd : p.P % 2 = 1)
    (value : Octets p.base p.publicValue p.len yb s) (length : yb.length = p.k)
    (scalar : Octets p.base p.privateValue p.len xb s) (positive : 0 < xb.length)
    (scalarLength : xb.length ≤ p.k) (count : p.slotValue 44 = BitVec.ofNat 32 xb.length)
    (valueStack : Region.Disjoint ⟨State.addr p.publicValue, yb.length⟩ ⟨State.addr s.sp, 72⟩)
    (scalarStack : Region.Disjoint ⟨State.addr p.privateValue, xb.length⟩ ⟨State.addr s.sp, 72⟩) :
    WP isa VG.Impl.Ffdh.Arm.Domain.CheckPrivate.main s fun t =>
      t.gpr .r0 = privateMainFlag p yb xb ∧ Frame (prepareAtWrites p s) s.mem t.mem := by
  have op0 : Operand 0 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have extend {m m' : Mem} (f : Frame [⟨State.addr p.base, 8 * p.len⟩] m m') : Frame (prepareAtWrites p s) m m' :=
    f.mono (by intro r hr; rw [List.mem_singleton] at hr; subst r; exact List.mem_cons_self)
  have pStack : Region.Disjoint ⟨State.addr p.domain, p.k⟩ ⟨State.addr s.sp, 72⟩ :=
    h.domainStack.sub_left (Region.sub_prefix (by rw [p.domainLength]; split <;> omega_using []))
  rw [VG.Impl.Ffdh.Arm.Domain.CheckPrivate.main, WP.seq_iff]
  refine WP.mono (prepareAt_ok s 24 h stable h24 h32 h0 h.pBytes p.pLength pStack large odd) ?_
  rintro u ⟨contextU, readyU, modU, r2U, frameU, restU⟩
  have sourceSep {src : BitVec 32} {bs : List Byte} (source : Octets p.base src p.len bs s)
      (stack : Region.Disjoint ⟨State.addr src, bs.length⟩ ⟨State.addr s.sp, 72⟩)
      (r : Region) (hr : r ∈ prepareAtWrites p s) : (⟨State.addr src, bs.length⟩ : Region).Disjoint r := by
    simp only [prepareAtWrites, prepareWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact source.separate
    · exact stack.sub_right (Offset.sub_base _ (by decide))
    · exact stack.sub_right (Offset.sub_base _ (by decide))
  have valueU := value.after_frame frameU restU (sourceSep value valueStack)
  have scalarU := scalar.after_frame frameU restU (sourceSep scalar scalarStack)
  rw [WP.seq_iff]
  refine WP.mono (importAt_ok u 1 40 44 contextU stable h40 h44 readyU (by decide) (by decide)
    scalarU positive (Nat.le_trans scalarLength p.width.2.2.2.1) count) ?_
  rintro v ⟨contextV, readyV, x, keepsV, frameV, restV⟩
  have fits : arrAt p.w 8 ≤ 8 * p.len := readyV.width ▸ readyV.layout.2.2.1
  have modV := (keeps_array_num keepsV fits op0 (by decide)).trans modU
  have r2V := (keeps_array_num keepsV fits op4 (by decide)).trans r2U
  rw [WP.seq_iff]
  refine WP.mono (scalarRange_ok v contextV stable h28 h32 h60 readyV modV odd) ?_
  rintro w ⟨contextW, readyW, flag, arraysW, frameW, restW⟩
  rw [x] at flag
  have modW := (arraysW 0 (by simp)).trans modV
  have r2W := (arraysW 4 (by simp)).trans r2V
  have valueW := (valueU.after_workspace frameV restV).after_workspace frameW restW
  have scalarW := (scalarU.after_workspace frameV restV).after_workspace frameW restW
  have fullW := (frameU.trans (extend frameV)).trans (extend frameW)
  rw [VG.Impl.Ffdh.Arm.Domain.ifFlag, WP.seq_iff]
  refine WP.mono (testFlag_ok w) ?_
  rintro z ⟨⟨zeroZ, memZ⟩, restZ⟩
  by_cases valid : 0 < Spec.Rsa.os2ip xb ∧ Spec.Rsa.os2ip xb < scalarBound p
  · refine WP.ite true (by change some (!z.z) = some true; rw [zeroZ, flag, scalarValidFlag, ite_eq_left valid]; rfl) ?_ (by intro hf; cases hf)
    intro _
    have ptrZ := (restZ.gpr .r0 (by simp)).trans contextW.ptr
    have contextZ := contextW.of_mem memZ restZ ptrZ
    have readyZ := readyW.of_mem memZ restZ ptrZ
    have frameZ : Frame [⟨State.addr p.base, 8 * p.len⟩] w.mem z.mem := by rw [memZ]; exact Frame.refl _ _
    refine WP.mono (privatePublic_ok z contextZ stable h28 h32 h36 h40 h44 h56 h60 readyZ
      (by rw [memZ]; exact modW) odd (by rw [memZ]; exact r2W)
      (valueW.after_workspace frameZ restZ) length (scalarW.after_workspace frameZ restZ) positive
      (by have := p.maxLength; omega_using [scalarLength, this]) count) ?_
    rintro t ⟨result, frameT⟩
    exact ⟨by rw [privateMainFlag, ite_eq_left valid]; exact result,
      (fullW.trans (extend frameZ)).trans (extend frameT)⟩
  · refine WP.ite false (by change some (!z.z) = some false; rw [zeroZ, flag, scalarValidFlag, ite_eq_right valid]; rfl) (by intro ht; cases ht) ?_
    intro _
    refine WP.mono (ret_ok z 2 (by decide)) ?_
    rintro t ⟨⟨result, memT⟩, _⟩
    exact ⟨by rw [result, privateMainFlag, ite_eq_right valid], by rw [memT, memZ]; exact fullW⟩

end VG.Proof.Ffdh.Arm
