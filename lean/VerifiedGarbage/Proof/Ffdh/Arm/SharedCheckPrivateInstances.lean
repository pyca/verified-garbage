module

public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Impl.Bignum.Arm.MontCall
public import VerifiedGarbage.Impl.Ffdh.Arm.SharedCheckPrivate
public import VerifiedGarbage.Proof.Ffdh.Arm.DomainCallMemory
public import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicPre
public import VerifiedGarbage.Proof.Ffdh.Arm.PrivateSpec
public import VerifiedGarbage.Proof.Ffdh.Arm.IncomingWord
public import VerifiedGarbage.Proof.Ffdh.Arm.SharedCheckPublicInstances
public import VerifiedGarbage.Proof.Ffdh.Arm.ScalarRange
public import VerifiedGarbage.Proof.Ffdh.Arm.ScalarRangeCT
public import VerifiedGarbage.Proof.Ffdh.Arm.Context
public import VerifiedGarbage.Proof.Ffdh.Arm.Octets
public import VerifiedGarbage.Proof.Ffdh.Arm.Frame
public import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicBody
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.RelCT
public import Init.Data.BitVec.Basic
public import VerifiedGarbage.Proof.Ffdh.Arm.DomainSharedPrepareAt
import VerifiedGarbage.Proof.Ffdh.Arm.DomainNormalizedPrepareAtCT
import VerifiedGarbage.Proof.Ffdh.Arm.SharedCheckPublicPower
import VerifiedGarbage.Proof.Ffdh.Arm.EntryStore
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Ffdh.Arm.Branch
import VerifiedGarbage.Proof.Ffdh.Arm.BranchCT
import VerifiedGarbage.Proof.Ffdh.Arm.Head
import VerifiedGarbage.Proof.Ffdh.Arm.HeadCT
import VerifiedGarbage.Proof.Ffdh.Arm.QTest
import VerifiedGarbage.Proof.Ffdh.Arm.ImportAt
import VerifiedGarbage.Proof.Ffdh.Arm.ImportAtCT
import VerifiedGarbage.Proof.Ffdh.Arm.Equal
import VerifiedGarbage.Proof.Ffdh.Arm.EqualCT
import VerifiedGarbage.Proof.Ffdh.Arm.Range
import VerifiedGarbage.Proof.Ffdh.Arm.RangeCT
import VerifiedGarbage.Proof.Ffdh.Arm.FlagCT
import VerifiedGarbage.Proof.Ffdh.Arm.FrameCT
import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
import VerifiedGarbage.Proof.Ffdh.Arm.PowerAtCT
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.TwoExpShared
import VerifiedGarbage.Proof.Bignum.Arm.TwoExpSharedCT
import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomery
import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomeryCT
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Lit
import Batteries.Logic
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst

/-! # `vg_ffdh_check_private` on ARMv7, generic over the RSA Montgomery product

The imported-private-key check (`Impl.Ffdh.Arm.SharedCheckPrivate`) whose
products call a shared Montgomery product (`MontBackend`), proven against
`Spec.Ffdh.checkPrivateContract` with the 48 bytes below its frame that the
product's calls use reserved (176 bytes in all): correct, constant time but
for the scalar's validity class that its status discloses, and satisfiable. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.SharedCheckPrivate
open VG VG.Arm VG.Arm.FrameStack VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt Operand arrAt)
open VG.Proof.X25519.Arm (Rest)

/-! ## The buffers outside the product's calls -/

/-- The domain, the public value and the scalar's `n` bytes are outside the
48 bytes below the stack pointer that the product's calls use. -/
structure CallMemory (p : Inputs) (n : Nat) (s : State) : Prop extends DomainCallMemory p s where
  scalarBelow : Region.Disjoint ⟨State.addr p.privateValue, n⟩ (belowA s.sp 48)

theorem CallMemory.of_outer {p : Inputs} {n : Nat} {s : State} {sp : BitVec 32}
    (fit : 176 ≤ sp.toNat) (pointer : s.sp = sp - BitVec.ofNat 32 128)
    (workspace : Region.Disjoint (belowA sp 176) ⟨State.addr p.base, 8 * p.len⟩)
    (domain : Region.Disjoint ⟨State.addr p.domain, p.dom.length⟩ (belowA sp 176))
    (publicValue : Region.Disjoint ⟨State.addr p.publicValue, p.k⟩ (belowA sp 176))
    (scalar : Region.Disjoint ⟨State.addr p.privateValue, n⟩ (belowA sp 176)) :
    CallMemory p n s := by
  have inner : Region.Sub (belowA s.sp 48) (belowA sp 176) := by
    rw [pointer]
    exact belowA_inner (a := 48) (k := 128) (by decide) fit
  exact ⟨DomainCallMemory.of_outer fit pointer workspace domain publicValue, scalar.sub_right inner⟩

theorem CallMemory.after {p : Inputs} {n : Nat} {s t : State} {rs : List Reg}
    (h : CallMemory p n s) (rest : Rest rs s t) : CallMemory p n t := by
  refine ⟨h.toDomainCallMemory.after rest, ?_⟩
  rw [rest.sp]
  exact h.scalarBelow

/-- The workspace and the 48 bytes below `sp`, what the product's calls write. -/
theorem below_separate {p : Inputs} {src : BitVec 32} {bs : List Byte} {s : State}
    (h : Octets p.base src p.len bs s) (below : Region.Disjoint ⟨State.addr src, bs.length⟩ (belowA s.sp 48)) :
    ∀ r ∈ [⟨State.addr p.base, 8 * p.len⟩, belowA s.sp 48],
      (⟨State.addr src, bs.length⟩ : Region).Disjoint r := by
  intro r hr
  rcases List.mem_cons.mp hr with hr | hr
  · subst r; exact h.separate
  · have eq := List.mem_singleton.mp hr; subst r; exact below

/-! ## The entry -/

/-- The arguments above the frame: the scalar, its length and the scratch. -/
structure Incoming (p : Inputs) (s : State) : Prop where
  scalar : IncomingWord p.privateValue 132 s
  scalarCount : IncomingWord (BitVec.ofNat 32 p.privateLength) 136 s
  scratch : IncomingWord p.base 140 s

theorem entry_ok (s : State) {p : Inputs} (h : ArgumentMemory p [] s)
    (incoming : Incoming p s) (domain : s.gpr .r0 = p.domain)
    (domainLength : s.gpr .r1 = BitVec.ofNat 32 p.dom.length) (count : s.gpr .r2 = BitVec.ofNat 32 p.k)
    (publicValue : s.gpr .r3 = p.publicValue) :
    WP isa (.block VG.Impl.Ffdh.Arm.Domain.CheckPrivate.entry) s fun t =>
      Context p [0, 44, 40, 36, 32, 28, 24] t ∧ Frame [⟨State.addr s.sp, 72⟩] s.mem t.mem := by
  unfold VG.Impl.Ffdh.Arm.Domain.CheckPrivate.entry VG.Impl.Ffdh.Arm.Domain.st
  refine wp_stackAddr (by decide) fun s0 moved => ?_
  obtain rest0 : Rest [.r12] s s0 := moved.rest (by simp)
  obtain args0 := h.of_mem moved.mem rest0
  obtain frame0 : Frame [⟨State.addr s.sp, 72⟩] s.mem s0.mem := by rw [moved.mem]; exact Frame.refl _ _
  obtain stack0 : s0.gpr .r12 = s0.sp := by rw [moved.gpr, moved.sp, BitVec.add_zero]
  refine wp_store_arg .r0 24 args0 (by decide) (by decide) (by decide)
    ((rest0.gpr .r0 (by simp)).trans domain) stack0 fun s1 args1 stepFrame1 stepRest1 => ?_
  obtain rest1 := rest0.trans (stepRest1.mono (by simp))
  obtain stack1 := (stepRest1.gpr .r12 (by simp)).trans (stack0.trans stepRest1.sp.symm)
  rw [rest0.sp] at stepFrame1
  obtain frame1 := frame0.trans stepFrame1
  refine wp_store_arg .r1 28 args1 (by decide) (by decide) (by decide)
    ((rest1.gpr .r1 (by simp)).trans domainLength) stack1 fun s2 args2 stepFrame2 stepRest2 => ?_
  obtain rest2 := rest1.trans (stepRest2.mono (by simp))
  obtain stack2 := (stepRest2.gpr .r12 (by simp)).trans (stack1.trans stepRest2.sp.symm)
  rw [rest1.sp] at stepFrame2
  obtain frame2 := frame1.trans stepFrame2
  refine wp_store_arg .r2 32 args2 (by decide) (by decide) (by decide)
    ((rest2.gpr .r2 (by simp)).trans count) stack2 fun s3 args3 stepFrame3 stepRest3 => ?_
  obtain rest3 := rest2.trans (stepRest3.mono (by simp))
  obtain stack3 := (stepRest3.gpr .r12 (by simp)).trans (stack2.trans stepRest3.sp.symm)
  rw [rest2.sp] at stepFrame3
  obtain frame3 := frame2.trans stepFrame3
  refine wp_store_arg .r3 36 args3 (by decide) (by decide) (by decide)
    ((rest3.gpr .r3 (by simp)).trans publicValue) stack3 fun s4 args4 stepFrame4 stepRest4 => ?_
  obtain rest4 := rest3.trans (stepRest4.mono (by simp))
  obtain stack4 := (stepRest4.gpr .r12 (by simp)).trans (stack3.trans stepRest4.sp.symm)
  rw [rest3.sp] at stepFrame4
  obtain frame4 := frame3.trans stepFrame4
  obtain allRest4 : Rest roundClobbers s s4 := rest4.mono (by simp [roundClobbers])
  refine wp_retain_incoming .r3 (by decide) args4 (by decide)
    (incoming.scalar.after (by decide) frame4 allRest4) (by decide) (by decide) (by decide) stack4
    fun s5 args5 stepFrame5 stepRest5 value5 stack5 => ?_
  obtain allRest5 := allRest4.trans (stepRest5.mono (by simp [roundClobbers]))
  rw [allRest4.sp] at stepFrame5
  obtain frame5 := frame4.trans stepFrame5
  refine wp_retain_incoming .r3 (by decide) args5 (by decide)
    (incoming.scalarCount.after (by decide) frame5 allRest5) (by decide) (by decide) (by decide) stack5
    fun s6 args6 stepFrame6 stepRest6 value6 stack6 => ?_
  obtain allRest6 := allRest5.trans (stepRest6.mono (by simp [roundClobbers]))
  rw [allRest5.sp] at stepFrame6
  obtain frame6 := frame5.trans stepFrame6
  refine wp_retain_incoming .r0 (by decide) args6 (by decide)
    (incoming.scratch.after (by decide) frame6 allRest6) (by decide) (by decide) (by decide) stack6
    fun s7 args7 stepFrame7 stepRest7 value7 stack7 => WP.block_nil ?_
  refine ⟨⟨args7, value7⟩, ?_⟩
  rw [allRest6.sp] at stepFrame7
  exact frame6.trans stepFrame7

/-! ## The checks, from the arithmetic's preparation -/

theorem match_ok (backend : MontBackend) (s : State) {p : Inputs} {slots : List Nat} {yb xb : List Byte}
    (h : Context p slots s) (calls : CallMemory p xb.length s) (stable : stableSlots slots = true)
    (h32 : 32 ∈ slots) (h36 : 36 ∈ slots) (h40 : 40 ∈ slots) (h44 : 44 ∈ slots) (h56 : 56 ∈ slots)
    (ready : ArithmeticReady p.base p.len p.w s)
    (modulus : numAt s.mem (State.addr p.base) p.w 0 = p.P) (odd : p.P % 2 = 1)
    (r2 : numAt s.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P)
    (value : Octets p.base p.publicValue p.len yb s) (length : yb.length = p.k)
    (scalar : Octets p.base p.privateValue p.len xb s) (positive : 0 < xb.length) (fits : xb.length < 2 ^ 32)
    (count : p.slotValue 44 = BitVec.ofNat 32 xb.length) :
    WP isa (VG.Impl.Ffdh.Arm.SharedCheckPrivate.matchPublic
      (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) s fun t =>
      t.gpr .r0 = privateMatchFlag p yb xb ∧
        Frame [⟨State.addr p.base, 8 * p.len⟩, belowA s.sp 48] s.mem t.mem := by
  have op1 : Operand 1 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op6 : Operand 6 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  rw [VG.Impl.Ffdh.Arm.SharedCheckPrivate.matchPublic, WP.seq_iff]
  refine WP.mono (sharedCheckPublicPower_ok backend s 56 40 44 h calls.toDomainCallMemory stable
    h56 h40 h44 h32 ready modulus odd r2 h.gBytes p.gLength scalar positive fits count calls.scalarBelow) ?_
  rintro u ⟨contextU, readyU, power, _, _, _, frameU, restU⟩
  have valueU := value.after_frame frameU restU
    (below_separate value (by rw [length]; exact calls.publicValue))
  rw [WP.seq_iff]
  refine WP.mono (importAt_ok u 1 36 32 contextU stable h36 h32 readyU (by decide) (by decide)
    valueU (by rw [length]; have := p.minLength; omega_using [this])
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
  exact ⟨by rw [result, flag]; rfl,
    by rw [memT]; exact (frameU.trans (frameV.mono (by simp))).trans (frameW.mono (by simp))⟩

theorem tail_ok (backend : MontBackend) (s : State) {p : Inputs} {slots : List Nat} {yb xb : List Byte}
    (h : Context p slots s) (calls : CallMemory p xb.length s) (stable : stableSlots slots = true)
    (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) (h36 : 36 ∈ slots) (h40 : 40 ∈ slots)
    (h44 : 44 ∈ slots) (h56 : 56 ∈ slots) (h60 : 60 ∈ slots)
    (ready : ArithmeticReady p.base p.len p.w s)
    (modulus : numAt s.mem (State.addr p.base) p.w 0 = p.P) (odd : p.P % 2 = 1)
    (r2 : numAt s.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P)
    (value : Octets p.base p.publicValue p.len yb s) (length : yb.length = p.k)
    (scalar : Octets p.base p.privateValue p.len xb s) (positive : 0 < xb.length) (fits : xb.length < 2 ^ 32)
    (count : p.slotValue 44 = BitVec.ofNat 32 xb.length) :
    WP isa (VG.Impl.Ffdh.Arm.SharedCheckPrivate.tail
      (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) s fun t =>
      t.gpr .r0 = privateTailFlag p yb xb ∧
        Frame [⟨State.addr p.base, 8 * p.len⟩, belowA s.sp 48] s.mem t.mem := by
  rw [VG.Impl.Ffdh.Arm.SharedCheckPrivate.tail, VG.Impl.Ffdh.Arm.Domain.withQ, WP.seq_iff]
  refine WP.mono (qTest_ok s h h28 h32) ?_
  rintro u ⟨⟨zero, memU⟩, restU⟩
  have ptrU := (restU.gpr .r0 (by simp)).trans h.ptr
  have contextU := h.of_mem memU restU ptrU
  have readyU := ready.of_mem memU restU ptrU
  have frameU : Frame [⟨State.addr p.base, 8 * p.len⟩, belowA s.sp 48] s.mem u.mem := by
    rw [memU]; exact Frame.refl _ _
  have callsU := calls.after restU
  have valueU := value.after_frame frameU restU
    (below_separate value (by rw [length]; exact calls.publicValue))
  have scalarU := scalar.after_frame frameU restU (below_separate scalar calls.scalarBelow)
  refine WP.ite p.hasQ (by simp only [eval, zero, Bool.not_not]) ?_ ?_
  · intro hasQ
    rw [WP.seq_iff]
    refine WP.mono (sharedCheckPublicSubgroup_ok backend u 36 contextU callsU.toDomainCallMemory stable
      h36 h60 h32 hasQ readyU (by rw [memU]; exact modulus) odd (by rw [memU]; exact r2) valueU length) ?_
    rintro v ⟨contextV, readyV, memberFlag, modV, r2V, frameV, restV⟩
    have callsV := callsU.after restV
    have valueV := valueU.after_frame frameV restV
      (below_separate valueU (by rw [length]; exact callsU.publicValue))
    have scalarV := scalarU.after_frame frameV restV (below_separate scalarU callsU.scalarBelow)
    rw [VG.Impl.Ffdh.Arm.Domain.ifFlag, WP.seq_iff]
    refine WP.mono (testFlag_ok v) ?_
    rintro w ⟨⟨zeroW, memW⟩, restW⟩
    have spV : v.sp = s.sp := restV.sp.trans restU.sp
    have frameUV : Frame [⟨State.addr p.base, 8 * p.len⟩, belowA s.sp 48] s.mem v.mem := by
      rw [restU.sp] at frameV; exact frameU.trans frameV
    by_cases member : Spec.Rsa.powMod (Spec.Rsa.os2ip yb) p.Q p.P = 1
    · refine WP.ite true (by change some (!w.z) = some true; rw [zeroW, memberFlag, ite_eq_left member]; rfl) ?_ (by intro hf; cases hf)
      intro _
      have ptrW := (restW.gpr .r0 (by simp)).trans contextV.ptr
      have contextW := contextV.of_mem memW restW ptrW
      have readyW := readyV.of_mem memW restW ptrW
      have frameW : Frame [⟨State.addr p.base, 8 * p.len⟩] v.mem w.mem := by rw [memW]; exact Frame.refl _ _
      refine WP.mono (match_ok backend w contextW (callsV.after restW) stable h32 h36 h40 h44 h56 readyW
        (by rw [memW]; exact modV) odd (by rw [memW]; exact r2V)
        (valueV.after_workspace frameW restW) length
        (scalarV.after_workspace frameW restW) positive fits count) ?_
      rintro t ⟨result, frameT⟩
      rw [restW.sp, spV] at frameT
      exact ⟨by rw [privateTailFlag, ite_eq_left hasQ, ite_eq_left member]; exact result,
        (frameUV.trans (frameW.mono (by simp))).trans frameT⟩
    · refine WP.ite false (by change some (!w.z) = some false; rw [zeroW, memberFlag, ite_eq_right member]; rfl) (by intro ht; cases ht) ?_
      intro _
      refine WP.mono (ret_ok w 0 (by decide)) ?_
      rintro t ⟨⟨result, memT⟩, _⟩
      exact ⟨by rw [result, privateTailFlag, ite_eq_left hasQ, ite_eq_right member], by rw [memT, memW]; exact frameUV⟩
  · intro hasQ
    refine WP.mono (match_ok backend u contextU callsU stable h32 h36 h40 h44 h56 readyU
      (by rw [memU]; exact modulus) odd (by rw [memU]; exact r2) valueU length scalarU positive fits count) ?_
    rintro t ⟨result, frameT⟩
    rw [restU.sp] at frameT
    exact ⟨by rw [privateTailFlag, ite_eq_right (by rw [hasQ]; decide)]; exact result, frameU.trans frameT⟩

theorem public_ok (backend : MontBackend) (s : State) {p : Inputs} {slots : List Nat} {yb xb : List Byte}
    (h : Context p slots s) (calls : CallMemory p xb.length s) (stable : stableSlots slots = true)
    (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) (h36 : 36 ∈ slots) (h40 : 40 ∈ slots)
    (h44 : 44 ∈ slots) (h56 : 56 ∈ slots) (h60 : 60 ∈ slots)
    (ready : ArithmeticReady p.base p.len p.w s)
    (modulus : numAt s.mem (State.addr p.base) p.w 0 = p.P) (odd : p.P % 2 = 1)
    (r2 : numAt s.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P)
    (value : Octets p.base p.publicValue p.len yb s) (length : yb.length = p.k)
    (scalar : Octets p.base p.privateValue p.len xb s) (positive : 0 < xb.length) (fits : xb.length < 2 ^ 32)
    (count : p.slotValue 44 = BitVec.ofNat 32 xb.length) :
    WP isa (VG.Impl.Ffdh.Arm.SharedCheckPrivate.publicCheck
      (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) s fun t =>
      t.gpr .r0 = privatePublicFlag p yb xb ∧
        Frame [⟨State.addr p.base, 8 * p.len⟩, belowA s.sp 48] s.mem t.mem := by
  have op0 : Operand 0 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op1 : Operand 1 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  unfold VG.Impl.Ffdh.Arm.SharedCheckPrivate.publicCheck
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
  have frameVW : Frame [⟨State.addr p.base, 8 * p.len⟩, belowA s.sp 48] s.mem w.mem :=
    (frameV.trans frameW).mono (by simp)
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
    refine WP.mono (tail_ok backend z contextZ (((calls.after restV).after restW).after restZ) stable
      h28 h32 h36 h40 h44 h56 h60 readyZ (by rw [memZ]; exact modW) odd (by rw [memZ]; exact r2W)
      (valueW.after_workspace frameZ restZ) length (scalarW.after_workspace frameZ restZ) positive fits count) ?_
    rintro t ⟨result, frameT⟩
    rw [memZ, restZ.sp, restW.sp, restV.sp] at frameT
    exact ⟨by rw [privatePublicFlag, ite_eq_left valid]; exact result, frameVW.trans frameT⟩
  · refine WP.ite false (by change some (!z.z) = some false; rw [zero, flag, ite_eq_right valid]; rfl) (by intro ht; cases ht) ?_
    intro _
    refine WP.mono (ret_ok z 0 (by decide)) ?_
    rintro t ⟨⟨result, memT⟩, _⟩
    exact ⟨by rw [privatePublicFlag, ite_eq_right valid]; exact result, by rw [memT, memZ]; exact frameVW⟩

theorem main_ok (backend : MontBackend) (s : State) {p : Inputs} {slots : List Nat} {yb xb : List Byte}
    (h : Context p slots s) (calls : CallMemory p xb.length s) (stable : stableSlots slots = true)
    (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots)
    (h36 : 36 ∈ slots) (h40 : 40 ∈ slots) (h44 : 44 ∈ slots) (h56 : 56 ∈ slots) (h60 : 60 ∈ slots)
    (large : 1 < p.P) (odd : p.P % 2 = 1)
    (value : Octets p.base p.publicValue p.len yb s) (length : yb.length = p.k)
    (scalar : Octets p.base p.privateValue p.len xb s) (positive : 0 < xb.length)
    (scalarLength : xb.length ≤ p.k) (count : p.slotValue 44 = BitVec.ofNat 32 xb.length)
    (valueStack : Region.Disjoint ⟨State.addr p.publicValue, yb.length⟩ ⟨State.addr s.sp, 72⟩)
    (scalarStack : Region.Disjoint ⟨State.addr p.privateValue, xb.length⟩ ⟨State.addr s.sp, 72⟩) :
    WP isa (VG.Impl.Ffdh.Arm.SharedCheckPrivate.main
      (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) s fun t =>
      t.gpr .r0 = privateMainFlag p yb xb ∧ Frame (domainPrepareWrites p s) s.mem t.mem := by
  have op0 : Operand 0 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have extend {m m' : Mem} (f : Frame [⟨State.addr p.base, 8 * p.len⟩] m m') :
      Frame (domainPrepareWrites p s) m m' :=
    f.mono (by intro r hr; rw [List.mem_singleton] at hr; subst r; simp [domainPrepareWrites, prepareAtWrites, prepareWrites])
  rw [VG.Impl.Ffdh.Arm.SharedCheckPrivate.main, WP.seq_iff]
  refine WP.mono (domainSharedPrepareAt24_ok backend s h calls.toDomainCallMemory stable h0 h24 h32 large odd) ?_
  rintro u ⟨contextU, readyU, modU, r2U, frameU, restU⟩
  have sourceSep {src : BitVec 32} {bs : List Byte} (source : Octets p.base src p.len bs s)
      (stack : Region.Disjoint ⟨State.addr src, bs.length⟩ ⟨State.addr s.sp, 72⟩)
      (below : Region.Disjoint ⟨State.addr src, bs.length⟩ (belowA s.sp 48))
      (r : Region) (hr : r ∈ domainPrepareWrites p s) : (⟨State.addr src, bs.length⟩ : Region).Disjoint r := by
    simp only [domainPrepareWrites, prepareAtWrites, prepareWrites, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl) | rfl
    · exact source.separate
    · exact stack.sub_right (Offset.sub_base _ (by decide))
    · exact stack.sub_right (Offset.sub_base _ (by decide))
    · exact below
  have valueU := value.after_frame frameU restU
    (sourceSep value valueStack (by rw [length]; exact calls.publicValue))
  have scalarU := scalar.after_frame frameU restU (sourceSep scalar scalarStack calls.scalarBelow)
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
    refine WP.mono (public_ok backend z contextZ ((((calls.after restU).after restV).after restW).after restZ)
      stable h28 h32 h36 h40 h44 h56 h60 readyZ
      (by rw [memZ]; exact modW) odd (by rw [memZ]; exact r2W)
      (valueW.after_workspace frameZ restZ) length (scalarW.after_workspace frameZ restZ) positive
      (by have := p.maxLength; omega_using [scalarLength, this]) count) ?_
    rintro t ⟨result, frameT⟩
    rw [memZ, restZ.sp, restW.sp, restV.sp, restU.sp] at frameT
    refine ⟨by rw [privateMainFlag, ite_eq_left valid]; exact result, fullW.trans (frameT.mono ?_)⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [domainPrepareWrites, prepareAtWrites, prepareWrites, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false]
    rcases hr with rfl | rfl
    · exact Or.inl (Or.inl rfl)
    · exact Or.inr rfl
  · refine WP.ite false (by change some (!z.z) = some false; rw [zeroZ, flag, scalarValidFlag, ite_eq_right valid]; rfl) (by intro ht; cases ht) ?_
    intro _
    refine WP.mono (ret_ok z 2 (by decide)) ?_
    rintro t ⟨⟨result, memT⟩, _⟩
    exact ⟨by rw [result, privateMainFlag, ite_eq_right valid], by rw [memT, memZ]; exact fullW⟩

theorem body_ok (backend : MontBackend) (s : State) {p : Inputs} {slots : List Nat} {yb xb : List Byte}
    (h : Context p slots s) (calls : CallMemory p xb.length s) (stable : stableSlots slots = true)
    (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) (h36 : 36 ∈ slots)
    (h40 : 40 ∈ slots) (h44 : 44 ∈ slots)
    (value : Octets p.base p.publicValue p.len yb s) (length : yb.length = p.k)
    (scalar : Octets p.base p.privateValue p.len xb s) (positive : 0 < xb.length)
    (scalarLength : xb.length ≤ p.k) (count : p.slotValue 44 = BitVec.ofNat 32 xb.length)
    (scalarStack : Region.Disjoint ⟨State.addr p.privateValue, xb.length⟩ ⟨State.addr s.sp, 72⟩)
    (valueStack : Region.Disjoint ⟨State.addr p.publicValue, yb.length⟩ ⟨State.addr s.sp, 72⟩) :
    WP isa (VG.Impl.Ffdh.Arm.Domain.head (VG.Impl.Ffdh.Arm.SharedCheckPrivate.main
      (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul))) s fun t =>
      t.gpr .r0 = checkedPrivateFlag p yb xb ∧ Frame (sharedPublicBodyWrites p s) s.mem t.mem := by
  unfold VG.Impl.Ffdh.Arm.Domain.head
  apply WP.assoc
  rw [WP.seq_iff]
  refine WP.mono (head_ok s h stable h0 h24 h32) ?_
  rintro u ⟨contextU, zero, frameU, restU⟩
  have fU : Frame (sharedPublicBodyWrites p s) s.mem u.mem :=
    frameU.mono (by simp [sharedPublicBodyWrites, bodyWrites])
  by_cases valid : Spec.Rsa.modulusValid p.P p.k = true
  · refine WP.ite true (by change some u.z = some true; rw [zero, valid]) ?_ (by intro hf; cases hf)
    intro _
    have facts := VG.Proof.Bignum.valid_facts valid p.minLength
    have stableU : stableSlots (60 :: 56 :: slots) = true := by
      change (true && (true && stableSlots slots)) = true
      rw [Bool.true_and, Bool.true_and, stable]
    have stackSep {src : BitVec 32} {bs : List Byte}
        (sep : Region.Disjoint ⟨State.addr src, bs.length⟩ ⟨State.addr s.sp, 72⟩)
        (r : Region) (hr : r ∈ [⟨State.addr s.sp, 72⟩]) : (⟨State.addr src, bs.length⟩ : Region).Disjoint r := by
      rw [List.mem_singleton] at hr; subst r; exact sep
    refine WP.mono (main_ok backend u contextU (calls.after restU) stableU
      (by simp [h0]) (by simp [h24]) (by simp [h28]) (by simp [h32]) (by simp [h36])
      (by simp [h40]) (by simp [h44]) (by simp) (by simp) facts.2.1 facts.1
      (value.after_frame frameU restU (stackSep valueStack)) length
      (scalar.after_frame frameU restU (stackSep scalarStack)) positive scalarLength count
      (by rw [restU.sp]; exact valueStack) (by rw [restU.sp]; exact scalarStack)) ?_
    rintro t ⟨result, frameT⟩
    refine ⟨?_, fU.trans (frameT.sub ?_)⟩
    · rw [checkedPrivateFlag, ite_eq_left valid]; exact result
    · intro r hr
      simp only [domainPrepareWrites, prepareAtWrites, prepareWrites, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hr
      rcases hr with (rfl | rfl | rfl) | rfl
      · exact ⟨⟨State.addr p.base, 8 * p.len⟩, by simp [sharedPublicBodyWrites, bodyWrites], by intro a ha; exact ha⟩
      · refine ⟨⟨State.addr s.sp, 72⟩, by simp [sharedPublicBodyWrites, bodyWrites], ?_⟩
        rw [restU.sp]
        exact Offset.sub_base _ (by decide)
      · refine ⟨⟨State.addr s.sp, 72⟩, by simp [sharedPublicBodyWrites, bodyWrites], ?_⟩
        rw [restU.sp]
        exact Offset.sub_base _ (by decide)
      · refine ⟨belowA s.sp 48, by simp [sharedPublicBodyWrites], ?_⟩
        rw [restU.sp]
        intro a ha; exact ha
  · have invalid : Spec.Rsa.modulusValid p.P p.k = false := Bool.eq_false_iff.mpr valid
    refine WP.ite false (by change some u.z = some false; rw [zero, invalid]) (by intro ht; cases ht) ?_
    intro _
    refine WP.mono (ret_ok u 0 (by decide)) ?_
    rintro t ⟨⟨result, memT⟩, _⟩
    exact ⟨by rw [checkedPrivateFlag, ite_eq_right valid]; exact result, by rw [memT]; exact fU⟩

/-! ## The function -/

theorem entered_ok (backend : MontBackend) (s : State) {p : Inputs} {yb xb : List Byte}
    (h : ArgumentMemory p [] s) (incoming : Incoming p s) (calls : CallMemory p xb.length s)
    (domain : s.gpr .r0 = p.domain) (domainLength : s.gpr .r1 = BitVec.ofNat 32 p.dom.length)
    (count : s.gpr .r2 = BitVec.ofNat 32 p.k) (publicValue : s.gpr .r3 = p.publicValue)
    (value : Octets p.base p.publicValue p.len yb s) (length : yb.length = p.k)
    (scalar : Octets p.base p.privateValue p.len xb s) (positive : 0 < xb.length)
    (scalarLength : xb.length ≤ p.k) (scalarCount : p.slotValue 44 = BitVec.ofNat 32 xb.length)
    (scalarStack : Region.Disjoint ⟨State.addr p.privateValue, xb.length⟩ ⟨State.addr s.sp, 72⟩)
    (valueStack : Region.Disjoint ⟨State.addr p.publicValue, yb.length⟩ ⟨State.addr s.sp, 72⟩) :
    WP isa (.seq (.block VG.Impl.Ffdh.Arm.Domain.CheckPrivate.entry)
      (VG.Impl.Ffdh.Arm.Domain.head (VG.Impl.Ffdh.Arm.SharedCheckPrivate.main
        (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)))) s fun t =>
      t.gpr .r0 = checkedPrivateFlag p yb xb ∧ Frame (sharedPublicBodyWrites p s) s.mem t.mem := by
  rw [WP.seq_iff]
  refine WP.mono (withAllRest (entry_ok s h incoming domain domainLength count publicValue)) ?_
  rintro u ⟨⟨contextU, frameU⟩, restU⟩
  have stackSep {src : BitVec 32} {bs : List Byte}
      (sep : Region.Disjoint ⟨State.addr src, bs.length⟩ ⟨State.addr s.sp, 72⟩)
      (r : Region) (hr : r ∈ [⟨State.addr s.sp, 72⟩]) : (⟨State.addr src, bs.length⟩ : Region).Disjoint r := by
    rw [List.mem_singleton] at hr; subst r; exact sep
  refine WP.mono (body_ok backend u contextU (calls.after restU) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (value.after_frame frameU restU (stackSep valueStack)) length
    (scalar.after_frame frameU restU (stackSep scalarStack)) positive scalarLength scalarCount
    (by rw [restU.sp]; exact scalarStack) (by rw [restU.sp]; exact valueStack)) ?_
  rintro t ⟨result, frameT⟩
  refine ⟨result, ?_⟩
  have entryFrame : Frame (sharedPublicBodyWrites p s) s.mem u.mem :=
    frameU.mono (by simp [sharedPublicBodyWrites, bodyWrites])
  change Frame [⟨State.addr p.base, 8 * p.len⟩, ⟨State.addr u.sp, 72⟩, belowA u.sp 48] u.mem t.mem at frameT
  rw [restU.sp] at frameT
  exact entryFrame.trans frameT

/-- What the precondition with a 128-byte reservation gives the function. -/
structure ArgsInput (p : Inputs) (yb xb : List Byte) (s : State) : Prop where
  stackFits : 128 ≤ s.sp.toNat
  args : ArgumentMemory p [] (entered s)
  incoming : Incoming p (entered s)
  domain : s.gpr .r0 = p.domain
  domainLength : s.gpr .r1 = BitVec.ofNat 32 p.dom.length
  count : s.gpr .r2 = BitVec.ofNat 32 p.k
  publicValue : s.gpr .r3 = p.publicValue
  value : Octets p.base p.publicValue p.len yb (entered s)
  length : yb.length = p.k
  scalar : Octets p.base p.privateValue p.len xb (entered s)
  positive : 0 < xb.length
  scalarLength : xb.length ≤ p.k
  scalarCount : p.slotValue 44 = BitVec.ofNat 32 xb.length
  scalarStack : Region.Disjoint ⟨State.addr p.privateValue, xb.length⟩ ⟨State.addr (entered s).sp, 72⟩
  valueStack : Region.Disjoint ⟨State.addr p.publicValue, yb.length⟩ ⟨State.addr (entered s).sp, 72⟩
  saved : ∀ r ∈ bodyWrites p (entered s), (⟨State.addr (pcPushed s).sp, 56⟩ : Region).Disjoint r

/-- What the precondition gives the function, with the 48 bytes below its frame. -/
structure FnInput (p : Inputs) (yb xb : List Byte) (s : State) : Prop where
  input : ArgsInput p yb xb s
  calls : CallMemory p xb.length (entered s)
  saved : ∀ r ∈ sharedPublicBodyWrites p (entered s),
    (⟨State.addr (pcPushed s).sp, 56⟩ : Region).Disjoint r

theorem fn_ok (backend : MontBackend) (s : State) {p : Inputs} {yb xb : List Byte} (h : FnInput p yb xb s) :
    WP isa (VG.Impl.Ffdh.Arm.SharedCheckPrivate.code
      (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) s fun t =>
      abiPreserved s t ∧ t.gpr .r0 = checkedPrivateFlag p yb xb := by
  unfold VG.Impl.Ffdh.Arm.SharedCheckPrivate.code
  refine framed_of_separate _ s h.input.stackFits (sharedPublicBodyWrites p (entered s))
    (fun _ status => status = checkedPrivateFlag p yb xb) h.saved ?_
  refine WP.mono (entered_ok backend (entered s) h.input.args h.input.incoming h.calls h.input.domain
    h.input.domainLength h.input.count h.input.publicValue h.input.value h.input.length h.input.scalar
    h.input.positive h.input.scalarLength h.input.scalarCount h.input.scalarStack h.input.valueStack) ?_
  rintro t ⟨result, frame⟩
  exact ⟨frame, result⟩

/-! ## From the precondition -/

theorem pre128 (s : State) (pre : (Spec.Ffdh.checkPrivateContract abi 176).pre s) :
    (Spec.Ffdh.checkPrivateContract abi 128).pre s := by
  sig_pre [Spec.Ffdh.checkPrivateContract, Spec.Ffdh.checkPrivateSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at pre ⊢
  obtain ⟨stackFit, argFit, rd, wr, domS, yS, xS, sArgs, stackDom, stackY, stackX, stackS, stackArgs,
    domFit, yFit, xFit, sFit, bounds, domainLen, yLen, xPositive, xMax, space⟩ := pre
  have inner : Region.Sub ⟨State.addr s.sp - BitVec.ofNat 64 128, 128⟩
      ⟨State.addr s.sp - BitVec.ofNat 64 176, 176⟩ :=
    Offset.below_mono _ (by decide) (by decide)
  exact ⟨by omega_using [stackFit], argFit, rd, wr, domS, yS, xS, sArgs, stackDom.sub_left inner,
    stackY.sub_left inner, stackX.sub_left inner, stackS.sub_left inner, stackArgs.sub_left inner,
    domFit, yFit, xFit, sFit, bounds, domainLen, yLen, xPositive, xMax, space⟩

theorem args_input (s : State) (pre : (Spec.Ffdh.checkPrivateContract abi 128).pre s)
    {p : Inputs} {yb xb : List Byte}
    (base : stackArg s 3 = p.base) (domain : s.gpr .r0 = p.domain) (peer : s.gpr .r3 = p.publicValue)
    (scalar : stackArg s 1 = p.privateValue) (count : (s.gpr .r2).toNat = p.k)
    (capacity : (stackArg s 4).toNat = p.len) (privateCount : (stackArg s 2).toNat = p.privateLength)
    (domainBytes : Spec.Rsa.bytesAt s.mem (State.addr p.domain) (s.gpr .r1).toNat = p.dom)
    (peerBytes : Spec.Rsa.bytesAt s.mem (State.addr p.publicValue) p.k = yb)
    (scalarBytes : Spec.Rsa.bytesAt s.mem (State.addr p.privateValue) p.privateLength = xb) :
    ArgsInput p yb xb s := by
  sig_pre [Spec.Ffdh.checkPrivateContract, Spec.Ffdh.checkPrivateSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at pre
  obtain ⟨stackFit, argFit, rd, wr, domS, yS, xS, sArgs, stackDom, stackY, stackX, stackS, stackArgs,
    domFit, yFit, xFit, sFit, _, _, yLen, xPositive, xMax, _⟩ := pre
  have domLen : (s.gpr .r1).toNat = p.dom.length := by
    have eq := congrArg List.length domainBytes
    simpa only [VG.Proof.Bignum.bytesAt_length] using eq
  have yLength : yb.length = p.k := by
    have eq := congrArg List.length peerBytes
    simpa only [VG.Proof.Bignum.bytesAt_length] using eq.symm
  have xLength : xb.length = p.privateLength := by
    have eq := congrArg List.length scalarBytes
    simpa only [VG.Proof.Bignum.bytesAt_length] using eq.symm
  rw [yLen, count] at rd yS stackY yFit
  rw [count] at xMax
  rw [privateCount] at rd xS stackX xFit xPositive xMax
  rw [domain, domLen] at rd domS stackDom domFit
  rw [peer] at rd yS stackY yFit
  rw [scalar] at rd xS stackX xFit
  rw [base, capacity, Nat.mul_comm p.len 8] at wr domS xS yS sArgs stackS sFit
  have reserved : State.addr s.sp - BitVec.ofNat 64 128 = State.addr (s.sp - BitVec.ofNat 32 128) :=
    (FrameStack.addr_sub' stackFit).symm
  simp only [State.addr] at reserved
  rw [reserved] at stackDom stackX stackY stackS stackArgs
  have ws : Workspace s p.base (8 * p.len) := ⟨sFit, by rw [wr]; simp [State.addr]⟩
  have domainRead : InRegions (s.rd ++ s.wr) (State.addr p.domain) p.dom.length :=
    ⟨⟨State.addr p.domain, p.dom.length⟩, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
  have peerRead : InRegions (s.rd ++ s.wr) (State.addr p.publicValue) p.k :=
    ⟨⟨State.addr p.publicValue, p.k⟩, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
  have scalarRead : InRegions (s.rd ++ s.wr) (State.addr p.privateValue) p.privateLength :=
    ⟨⟨State.addr p.privateValue, p.privateLength⟩, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
  have rootDomain : Octets p.base p.domain p.len p.dom s :=
    ⟨domFit, domainRead, domS, by rw [← domLen]; exact domainBytes⟩
  have rootPeer : Octets p.base p.publicValue p.len yb s :=
    ⟨by rw [yLength]; exact yFit, by rw [yLength]; exact peerRead,
      by rw [yLength]; exact yS, by rw [yLength]; exact peerBytes⟩
  have rootScalar : Octets p.base p.privateValue p.len xb s :=
    ⟨by rw [xLength]; exact xFit, by rw [xLength]; exact scalarRead,
      by rw [xLength]; exact xS, by rw [xLength]; exact scalarBytes⟩
  have args : ArgumentMemory p [] (entered s) :=
    ⟨entered_workspace ws, entered_locals s stackFit stackS, entered_octets rootDomain stackFit stackDom,
      stackDom.symm.sub_right (locals_sub_reserved s stackFit), by simp⟩
  have argStart : stackArgAddr s 0 = State.addr s.sp := by simp [stackArgAddr]
  have argAddr (i : Nat) (hi : i < 5) : stackArgAddr s i = off (State.addr s.sp) (4 * i) :=
    VG.Arm.addr_add (by omega_using [argFit, hi])
  have argSub (i : Nat) (hi : i < 5) :
      (⟨stackArgAddr s i, 4⟩ : Region).Sub ⟨stackArgAddr s 0, 20⟩ := by
    rw [argStart, argAddr i hi]; exact Offset.sub_base _ (by omega_using [hi])
  have incoming (i : Nat) (hi : i < 5) : IncomingWord (stackArg s i) (128 + 4 * i) (entered s) :=
    enteredIncoming s stackFit (by omega_using [argFit, hi])
      ⟨⟨stackArgAddr s 0, 20⟩, List.mem_append_left _ (by rw [rd]; simp), by
        rw [argStart, argAddr i hi]; exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
      (stackArgs.sub_right (argSub i hi)) rfl
  have nativeIncoming : Incoming p (entered s) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [← scalar]; exact incoming 1 (by decide)
    · have h := incoming 2 (by decide)
      rw [← privateCount, BitVec.ofNat_toNat, BitVec.setWidth_eq]; exact h
    · rw [← base]; exact incoming 3 (by decide)
  refine ⟨stackFit, args, nativeIncoming, domain, ?_, ?_, peer,
    entered_octets rootPeer stackFit (by rw [yLength]; exact stackY), yLength,
    entered_octets rootScalar stackFit (by rw [xLength]; exact stackX),
    by rw [xLength]; omega_using [xPositive], by rw [xLength]; exact xMax, ?_, ?_, ?_, ?_⟩
  · rw [← domLen, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [← count, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · change BitVec.ofNat 32 p.privateLength = _; rw [xLength]
  · rw [xLength]; exact stackX.symm.sub_right (locals_sub_reserved s stackFit)
  · rw [yLength]; exact stackY.symm.sub_right (locals_sub_reserved s stackFit)
  · intro r hr
    simp only [bodyWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact stackS.sub_left (saved_sub_reserved s stackFit)
    · exact saved_separate_locals s stackFit

theorem input (s : State) (pre : (Spec.Ffdh.checkPrivateContract abi 176).pre s)
    {p : Inputs} {yb xb : List Byte}
    (base : stackArg s 3 = p.base) (domain : s.gpr .r0 = p.domain) (peer : s.gpr .r3 = p.publicValue)
    (scalar : stackArg s 1 = p.privateValue) (count : (s.gpr .r2).toNat = p.k)
    (capacity : (stackArg s 4).toNat = p.len) (privateCount : (stackArg s 2).toNat = p.privateLength)
    (domainBytes : Spec.Rsa.bytesAt s.mem (State.addr p.domain) (s.gpr .r1).toNat = p.dom)
    (peerBytes : Spec.Rsa.bytesAt s.mem (State.addr p.publicValue) p.k = yb)
    (scalarBytes : Spec.Rsa.bytesAt s.mem (State.addr p.privateValue) p.privateLength = xb) :
    FnInput p yb xb s := by
  have old := args_input s (pre128 s pre) base domain peer scalar count capacity privateCount
    domainBytes peerBytes scalarBytes
  sig_pre [Spec.Ffdh.checkPrivateContract, Spec.Ffdh.checkPrivateSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at pre
  obtain ⟨stackFit, _, _, _, _, _, _, _, stackDom, stackY, stackX, stackS, _,
    _, _, _, _, _, _, yLen, _, _, _⟩ := pre
  have domLen : (s.gpr .r1).toNat = p.dom.length := by
    have eq := congrArg List.length domainBytes
    simpa only [VG.Proof.Bignum.bytesAt_length] using eq
  have xLen : xb.length = p.privateLength := by
    have eq := congrArg List.length scalarBytes
    simpa only [VG.Proof.Bignum.bytesAt_length] using eq.symm
  rw [yLen, count, peer] at stackY
  rw [privateCount, scalar] at stackX
  rw [domain, domLen] at stackDom
  rw [base, capacity, Nat.mul_comm p.len 8] at stackS
  have reserved : State.addr s.sp - BitVec.ofNat 64 176 = State.addr (s.sp - BitVec.ofNat 32 176) :=
    (addr_sub' stackFit).symm
  simp only [State.addr] at reserved
  rw [reserved] at stackDom stackY stackX stackS
  have calls := CallMemory.of_outer (p := p) (n := xb.length) stackFit (entered_sp s)
    stackS stackDom.symm stackY.symm (by rw [xLen]; exact stackX.symm)
  refine ⟨old, calls, ?_⟩
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact old.saved r hr
  · have eq := List.mem_singleton.mp hr
    subst r
    have shifted : (pcPushed s).sp = (entered s).sp + BitVec.ofNat 32 72 := (BitVec.sub_add_cancel _ _).symm
    have fit : (entered s).sp.toNat + 72 < 2^32 := by
      rw [entered_nat s (by omega_using [stackFit])]; have := s.sp.isLt; omega_using []
    rw [shifted, VG.Arm.addr_add fit, belowA, addr_sub' calls.stack.fit]
    exact (Offset.disjoint_below_above _ (m:=48) (a:=72) (l:=56) (by decide)).symm

theorem data (s : State) (pre : (Spec.Ffdh.checkPrivateContract abi 176).pre s) :
    ∃ (p : Inputs) (yb xb : List Byte), stackArg s 3 = p.base ∧ s.gpr .r0 = p.domain ∧
      s.gpr .r3 = p.publicValue ∧ stackArg s 1 = p.privateValue ∧ (s.gpr .r2).toNat = p.k ∧
      (stackArg s 4).toNat = p.len ∧ (stackArg s 2).toNat = p.privateLength ∧
      Spec.Rsa.bytesAt s.mem (State.addr p.domain) (s.gpr .r1).toNat = p.dom ∧
      Spec.Rsa.bytesAt s.mem (State.addr p.publicValue) p.k = yb ∧
      Spec.Rsa.bytesAt s.mem (State.addr p.privateValue) p.privateLength = xb ∧ FnInput p yb xb s := by
  have original := pre
  sig_pre [Spec.Ffdh.checkPrivateContract, Spec.Ffdh.checkPrivateSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at pre
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, bounds, domainLen, _, _, _, space⟩ := pre
  let dom := Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat
  have domLength : dom.length = (s.gpr .r1).toNat := VG.Proof.Bignum.bytesAt_length _ _ _
  let p : Inputs := {
    base := stackArg s 3
    domain := s.gpr .r0
    publicValue := s.gpr .r3
    privateValue := stackArg s 1
    output := 0
    entropy := 0
    len := (stackArg s 4).toNat
    k := (s.gpr .r2).toNat
    privateLength := (stackArg s 2).toNat
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
      · rename_i different
        rcases domainLen with h | h
        · exact h
        · exact False.elim (different h) }
  let yb := Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r3)) (s.gpr .r2).toNat
  let xb := Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 1)) (stackArg s 2).toNat
  exact ⟨p, yb, xb, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    input s original (p := p) (yb := yb) (xb := xb) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩

/-- One imported-private-key check for every shared Montgomery product. -/
def code (b : MontBackend) : Prog isa :=
  VG.Impl.Ffdh.Arm.SharedCheckPrivate.code (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul)

theorem correct (backend : MontBackend) (s : State) (pre : (Spec.Ffdh.checkPrivateContract abi 176).pre s) :
    ∃ tr t, Exec isa (code backend) s tr t ∧
      abiPreserved s t ∧ (Spec.Ffdh.checkPrivateContract abi 176).post s t := by
  obtain ⟨p, yb, xb, _, domain, peer, scalar, count, _, privateCount,
    domainBytes, peerBytes, scalarBytes, input⟩ := data s pre
  obtain ⟨tr, t, run, preserved, result⟩ := fn_ok backend s input
  refine ⟨tr, t, run, preserved, ?_⟩
  have length : (stackArg s 0).toNat = (s.gpr .r2).toNat := by
    sig_pre [Spec.Ffdh.checkPrivateContract, Spec.Ffdh.checkPrivateSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at pre
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, length, _, _, _⟩ := pre
    exact length
  sig_post [Spec.Ffdh.checkPrivateContract, Spec.Ffdh.checkPrivateSig, abi, argRegs, reduceClassify, Loc.val, State.addr]
  rw [BitVec.setWidth_append_eq_right]
  simp only [State.addr] at domainBytes peerBytes scalarBytes
  simp only [length, count, domain, peer, scalar, privateCount, domainBytes, peerBytes, scalarBytes]
  intro valid
  rw [result]
  exact checkedPrivateFlag_spec p yb xb valid

/-! ## Constant time -/

/-- The arithmetic prepared, with the public value, the scalar and the buffers
outside the product's calls. -/
structure Ready (p : Inputs) (slots : List Nat) (yb xb : List Byte) (s : State) : Prop where
  context : Context p slots s
  ready : ArithmeticReady p.base p.len p.w s
  modulus : numAt s.mem (State.addr p.base) p.w 0 = p.P
  r2 : numAt s.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P
  value : Octets p.base p.publicValue p.len yb s
  scalar : Octets p.base p.privateValue p.len xb s
  calls : CallMemory p xb.length s

theorem Ready.after_mem {p : Inputs} {slots : List Nat} {yb xb : List Byte} {s t : State} {rs : List Reg}
    (h : Ready p slots yb xb s) (mem : t.mem = s.mem) (rest : Rest rs s t)
    (ptr : t.gpr .r0 = p.base) : Ready p slots yb xb t := by
  have frame : Frame [⟨State.addr p.base, 8 * p.len⟩] s.mem t.mem := by rw [mem]; exact Frame.refl _ _
  exact ⟨h.context.of_mem mem rest ptr, h.ready.of_mem mem rest ptr, by rw [mem]; exact h.modulus,
    by rw [mem]; exact h.r2, h.value.after_workspace frame rest, h.scalar.after_workspace frame rest,
    h.calls.after rest⟩

theorem Ready.after_workspace {p : Inputs} {slots : List Nat} {yb xb : List Byte} {s t : State} {rs : List Reg}
    (h : Ready p slots yb xb s) (stable : stableSlots slots = true)
    (frame : Frame [⟨State.addr p.base, 8 * p.len⟩] s.mem t.mem) (rest : Rest rs s t)
    (ready : ArithmeticReady p.base p.len p.w t) (modulus : numAt t.mem (State.addr p.base) p.w 0 = p.P)
    (r2 : numAt t.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P) : Ready p slots yb xb t :=
  ⟨h.context.after_workspace frame rest ready.ptr (fun d hd => (stableSlots_at (d := d) stable hd).1),
    ready, modulus, r2, h.value.after_workspace frame rest, h.scalar.after_workspace frame rest,
    h.calls.after rest⟩

theorem match_ct (backend : MontBackend) {p : Inputs} {slots : List Nat} {yb xb1 xb2 : List Byte}
    (stable : stableSlots slots = true) (h32 : 32 ∈ slots) (h36 : 36 ∈ slots)
    (h40 : 40 ∈ slots) (h44 : 44 ∈ slots) (h56 : 56 ∈ slots)
    (peerLength : yb.length = p.k) (positive : 0 < xb1.length) (fits : xb1.length < 2 ^ 32)
    (count : p.slotValue 44 = BitVec.ofNat 32 xb1.length) (length : xb1.length = xb2.length) (odd : p.P % 2 = 1) :
    RelCT isa (fun s t => Ready p slots yb xb1 s ∧ Ready p slots yb xb2 t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.SharedCheckPrivate.matchPublic
        (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) (fun _ _ => True) := by
  have powers : RelCT isa (fun s t => Ready p slots yb xb1 s ∧ Ready p slots yb xb2 t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.SharedCheckPublic.powerAt
        (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) 56 40 44) (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    let correct := fun o a b ho ha hb z input => backend.correct z (base := p.base) (len := p.len) (w := p.w)
      (o := o) (a := a) (b := b) input ho ha hb
    let K := TwoExp.sharedMontgomery p.base s.sp p.len p.w backend.name backend.mul correct backend.stackOk
    have timing : TwoExp.MontgomeryTiming K :=
      TwoExp.sharedMontgomeryTiming p.base s.sp p.len p.w backend.name backend.mul correct backend.stackOk
        (fun _ _ _ ho ha hb => backend.rawCT ho ha hb)
    have separate : ∀ r ∈ [⟨State.addr p.base, 8 * p.len⟩, belowA s.sp 48],
        Region.Disjoint ⟨State.addr (p.slotValue 40), xb1.length⟩ r :=
      below_separate h.1.scalar h.1.calls.scalarBelow
    have input (a : State) {xb : List Byte} (ha : Ready p slots yb xb a) :
        PowerAtInput p slots 56 40 p.P ((p.dom.drop p.k).take p.k) xb a :=
      ⟨ha.context, ha.ready, ha.modulus, ha.r2, ha.context.gBytes, ha.scalar⟩
    have run := (sharedCheckPublicPowerAt_ct K timing stable h56 h40 h44 h32
      p.gLength positive fits count length odd separate).mono
      (P' := fun (a b : State) => (Ready p slots yb xb1 a ∧ a.sp = s.sp) ∧
        (Ready p slots yb xb2 b ∧ b.sp = s.sp) ∧ a.sp = b.sp)
      (fun _ _ hab => ⟨⟨input _ hab.1.1, hab.1.1.calls.stack, hab.1.2⟩,
        ⟨input _ hab.2.1.1, hab.2.1.1.calls.stack, hab.2.1.2⟩, hab.2.2⟩)
      (fun _ _ hx => hx)
    exact run s t tr1 tr2 u v ⟨⟨h.1, rfl⟩, ⟨h.2.1, h.2.2.symm⟩, h.2.2⟩ e1 e2
  have wpPower (s : State) {xb : List Byte} (h : Ready p slots yb xb s)
      (positive : 0 < xb.length) (fits : xb.length < 2 ^ 32) (count : p.slotValue 44 = BitVec.ofNat 32 xb.length) :
      WP isa (VG.Impl.Ffdh.Arm.SharedCheckPublic.powerAt
        (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) 56 40 44) s (Ready p slots yb xb) := by
    refine WP.mono (sharedCheckPublicPower_ok backend s 56 40 44 h.context h.calls.toDomainCallMemory stable
      h56 h40 h44 h32 h.ready h.modulus odd h.r2 h.context.gBytes p.gLength h.scalar positive fits count
      h.calls.scalarBelow) ?_
    rintro u ⟨context, ready, _, modulus, r2, _, frame, rest⟩
    exact ⟨context, ready, modulus, r2,
      h.value.after_frame frame rest (below_separate h.value (by rw [peerLength]; exact h.calls.publicValue)),
      h.scalar.after_frame frame rest (below_separate h.scalar h.calls.scalarBelow), h.calls.after rest⟩
  have imports := (importAt_ct (p := p) (a := 1) (slot := 36) (k := p.k)
    stable h36 h32 rfl (by decide)).mono
    (P' := fun (s t : State) => Ready p slots yb xb1 s ∧ Ready p slots yb xb2 t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨⟨h.1.context, h.1.ready⟩, ⟨h.2.1.context, h.2.1.ready⟩, h.2.2⟩) (fun _ _ h => h)
  have wpImport (s : State) {xb : List Byte} (h : Ready p slots yb xb s) :
      WP isa (VG.Impl.Ffdh.Arm.Domain.importAt 1 36 32) s (ArithmeticReady p.base p.len p.w) :=
    WP.mono (importAt_ok s 1 36 32 h.context stable h36 h32 h.ready (by decide) (by decide) h.value
      (by rw [peerLength]; have := p.minLength; omega) (by rw [peerLength]; exact p.width.2.2.2.1)
      (by change BitVec.ofNat 32 p.k = _; rw [peerLength])) fun _ j => j.2.1
  have equal := equal_ct (base := p.base) (len := p.len) (w := p.w)
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp] : Operand 6)
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp] : Operand 1)
  unfold VG.Impl.Ffdh.Arm.SharedCheckPrivate.matchPublic
  exact relCT_chain powers (fun s h => wpPower s h positive fits count)
    (fun s h => wpPower s h (by rw [← length]; exact positive)
      (by rw [← length]; exact fits) (by rw [← length]; exact count))
    (relCT_chain imports (fun s h => wpImport s h) (fun s h => wpImport s h) (equal.seq finishFlag_ct))

/-- `Ready`, with the public value's subgroup membership in the flag. -/
structure Member (p : Inputs) (slots : List Nat) (yb xb : List Byte) (s : State) : Prop extends
    Ready p slots yb xb s where
  flag : s.gpr .r11 = if Spec.Rsa.powMod (Spec.Rsa.os2ip yb) p.Q p.P = 1 then 1 else 0

theorem Member.after_mem {p : Inputs} {slots : List Nat} {yb xb : List Byte} {s t : State}
    (h : Member p slots yb xb s) (mem : t.mem = s.mem) (rest : Rest [] s t) :
    Member p slots yb xb t :=
  ⟨h.toReady.after_mem mem rest ((rest.gpr .r0 (by simp)).trans h.context.ptr),
    (rest.gpr .r11 (by simp)).trans h.flag⟩

theorem tail_ct (backend : MontBackend) {p : Inputs} {slots : List Nat} {yb xb1 xb2 : List Byte}
    (stable : stableSlots slots = true) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) (h36 : 36 ∈ slots)
    (h40 : 40 ∈ slots) (h44 : 44 ∈ slots) (h56 : 56 ∈ slots) (h60 : 60 ∈ slots)
    (peerLength : yb.length = p.k) (positive : 0 < xb1.length) (fits : xb1.length < 2 ^ 32)
    (count : p.slotValue 44 = BitVec.ofNat 32 xb1.length) (length : xb1.length = xb2.length) (odd : p.P % 2 = 1) :
    RelCT isa (fun s t => Ready p slots yb xb1 s ∧ Ready p slots yb xb2 t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.SharedCheckPrivate.tail
        (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) (fun _ _ => True) := by
  let Q := fun (xb : List Byte) (s : State) => Ready p slots yb xb s ∧ s.z = !p.hasQ
  have tests := qTest_ct.mono
    (P' := fun (s t : State) => Ready p slots yb xb1 s ∧ Ready p slots yb xb2 t ∧ s.sp = t.sp)
    (fun _ _ h => h.2.2) (fun _ _ _ => trivial)
  have wpTest (s : State) {xb : List Byte} (h : Ready p slots yb xb s) :
      WP isa VG.Impl.Ffdh.Arm.Domain.qTest s (Q xb) := by
    refine WP.mono (qTest_ok s h.context h28 h32) ?_
    rintro u ⟨⟨zero, mem⟩, rest⟩
    exact ⟨h.after_mem mem rest ((rest.gpr .r0 (by simp)).trans h.context.ptr), zero⟩
  have matchCT := match_ct backend stable h32 h36 h40 h44 h56 peerLength positive fits count length odd
  have branches : RelCT isa (fun s t => Q xb1 s ∧ Q xb2 t ∧ s.sp = t.sp)
      (.ite .ne (.seq (VG.Impl.Ffdh.Arm.SharedCheckPublic.subgroup
          (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) 36)
        (VG.Impl.Ffdh.Arm.Domain.ifFlag (VG.Impl.Ffdh.Arm.SharedCheckPrivate.matchPublic
          (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) (VG.Impl.Ffdh.Arm.Domain.ret 0)))
        (VG.Impl.Ffdh.Arm.SharedCheckPrivate.matchPublic
          (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul))) (fun _ _ => True) := by
    apply iteKnownPair_ct p.hasQ (fun s h => by simp only [eval, h.2, Bool.not_not])
      (fun s h => by simp only [eval, h.2, Bool.not_not])
    · intro hasQ
      have subgroup := (sharedCheckPublicSubgroup_ct backend stable h36 h60 h32 hasQ peerLength odd).mono
        (P' := fun (s t : State) => Ready p slots yb xb1 s ∧ Ready p slots yb xb2 t ∧ s.sp = t.sp)
        (fun _ _ h => ⟨⟨⟨h.1.context, h.1.ready, h.1.modulus, h.1.r2, h.1.value⟩, h.1.calls.toDomainCallMemory⟩,
          ⟨⟨h.2.1.context, h.2.1.ready, h.2.1.modulus, h.2.1.r2, h.2.1.value⟩, h.2.1.calls.toDomainCallMemory⟩,
          h.2.2⟩) (fun _ _ h => h)
      have wpSubgroup (s : State) {xb : List Byte} (h : Ready p slots yb xb s) :
          WP isa (VG.Impl.Ffdh.Arm.SharedCheckPublic.subgroup
            (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) 36) s (Member p slots yb xb) := by
        refine WP.mono (sharedCheckPublicSubgroup_ok backend s 36 h.context h.calls.toDomainCallMemory stable
          h36 h60 h32 hasQ h.ready h.modulus odd h.r2 h.value peerLength) ?_
        rintro u ⟨context, ready, flag, modulus, r2, frame, rest⟩
        exact ⟨⟨context, ready, modulus, r2,
          h.value.after_frame frame rest (below_separate h.value (by rw [peerLength]; exact h.calls.publicValue)),
          h.scalar.after_frame frame rest (below_separate h.scalar h.calls.scalarBelow), h.calls.after rest⟩, flag⟩
      have matched : RelCT isa (fun s t => Member p slots yb xb1 s ∧ Member p slots yb xb2 t ∧ s.sp = t.sp)
          (VG.Impl.Ffdh.Arm.Domain.ifFlag (VG.Impl.Ffdh.Arm.SharedCheckPrivate.matchPublic
            (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) (VG.Impl.Ffdh.Arm.Domain.ret 0))
          (fun _ _ => True) := by
        apply ifFlag_pair_ct (decide (Spec.Rsa.powMod (Spec.Rsa.os2ip yb) p.Q p.P = 1))
          (fun _ h => by simpa only [decide_eq_true_eq] using h.flag)
          (fun _ h => by simpa only [decide_eq_true_eq] using h.flag)
          (fun _ _ h mem rest => h.after_mem mem rest) (fun _ _ h mem rest => h.after_mem mem rest)
        · intro _
          exact matchCT.mono (fun _ _ h => ⟨h.1.toReady, h.2.1.toReady, h.2.2⟩) (fun _ _ h => h)
        · intro _
          exact (ret_ct 0).mono (fun _ _ _ => trivial) (fun _ _ h => h)
      exact (relCT_chain subgroup (fun s h => wpSubgroup s h) (fun s h => wpSubgroup s h) matched).mono
        (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ h => h)
    · intro _
      exact matchCT.mono (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.SharedCheckPrivate.tail VG.Impl.Ffdh.Arm.Domain.withQ
  exact relCT_chain tests (fun s h => wpTest s h) (fun s h => wpTest s h) branches

/-- `Ready`, with the public value imported. -/
structure Imported (p : Inputs) (slots : List Nat) (yb xb : List Byte) (s : State) : Prop extends
    Ready p slots yb xb s where
  imported : numAt s.mem (State.addr p.base) p.w 1 = Spec.Rsa.os2ip yb

/-- `Ready`, with the public value's range in the flag. -/
structure Ranged (p : Inputs) (slots : List Nat) (yb xb : List Byte) (s : State) : Prop extends
    Ready p slots yb xb s where
  flag : s.gpr .r11 = if 1 < Spec.Rsa.os2ip yb ∧ Spec.Rsa.os2ip yb < p.P - 1 then 1 else 0

theorem Ranged.after_mem {p : Inputs} {slots : List Nat} {yb xb : List Byte} {s t : State}
    (h : Ranged p slots yb xb s) (mem : t.mem = s.mem) (rest : Rest [] s t) :
    Ranged p slots yb xb t :=
  ⟨h.toReady.after_mem mem rest ((rest.gpr .r0 (by simp)).trans h.context.ptr),
    (rest.gpr .r11 (by simp)).trans h.flag⟩

theorem import_public (s : State) {p : Inputs} {slots : List Nat} {yb xb : List Byte}
    (h : Ready p slots yb xb s) (stable : stableSlots slots = true) (h36 : 36 ∈ slots) (h32 : 32 ∈ slots)
    (length : yb.length = p.k) :
    WP isa (VG.Impl.Ffdh.Arm.Domain.importAt 1 36 32) s (Imported p slots yb xb) := by
  have op0 : Operand 0 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  refine WP.mono (importAt_ok s 1 36 32 h.context stable h36 h32 h.ready (by decide) (by decide) h.value
    (by rw [length]; have := p.minLength; omega) (by rw [length]; exact p.width.2.2.2.1)
    (by change BitVec.ofNat 32 p.k = _; rw [length])) ?_
  rintro u ⟨context, ready, value, keeps, frame, rest⟩
  have fits : arrAt p.w 8 ≤ 8 * p.len := ready.width ▸ ready.layout.2.2.1
  exact ⟨⟨context, ready, (keeps_array_num keeps fits op0 (by decide)).trans h.modulus,
    (keeps_array_num keeps fits op4 (by decide)).trans h.r2,
    h.value.after_workspace frame rest, h.scalar.after_workspace frame rest, h.calls.after rest⟩, value⟩

theorem range_public (s : State) {p : Inputs} {slots : List Nat} {yb xb : List Byte}
    (h : Imported p slots yb xb s) (stable : stableSlots slots = true) (odd : p.P % 2 = 1) :
    WP isa (VG.Impl.Ffdh.Arm.inRange 1) s (Ranged p slots yb xb) := by
  have op0 : Operand 0 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op1 : Operand 1 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  refine WP.mono (inRange_ok s h.ready op1 (by decide) (by rw [h.modulus]; exact odd)) ?_
  rintro u ⟨ready, flag, arrays, frame, rest⟩
  rw [h.imported, h.modulus] at flag
  exact ⟨h.toReady.after_workspace stable frame rest ready
    ((arrays 0 op0 (by decide)).trans h.modulus) ((arrays 4 op4 (by decide)).trans h.r2), flag⟩

theorem public_ct (backend : MontBackend) {p : Inputs} {slots : List Nat} {yb xb1 xb2 : List Byte}
    (stable : stableSlots slots = true) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) (h36 : 36 ∈ slots)
    (h40 : 40 ∈ slots) (h44 : 44 ∈ slots) (h56 : 56 ∈ slots) (h60 : 60 ∈ slots)
    (peerLength : yb.length = p.k) (positive : 0 < xb1.length) (fits : xb1.length < 2 ^ 32)
    (count : p.slotValue 44 = BitVec.ofNat 32 xb1.length) (length : xb1.length = xb2.length) (odd : p.P % 2 = 1) :
    RelCT isa (fun s t => Ready p slots yb xb1 s ∧ Ready p slots yb xb2 t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.SharedCheckPrivate.publicCheck
        (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) (fun _ _ => True) := by
  have imports := (importAt_ct (p := p) (a := 1) (slot := 36) (k := p.k)
    stable h36 h32 rfl (by decide)).mono
    (P' := fun (s t : State) => Ready p slots yb xb1 s ∧ Ready p slots yb xb2 t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨⟨h.1.context, h.1.ready⟩, ⟨h.2.1.context, h.2.1.ready⟩, h.2.2⟩) (fun _ _ h => h)
  have ranges := (inRange_ct (base := p.base) (len := p.len) (w := p.w)
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp] : Operand 1) (by decide)).mono
    (P' := fun (s t : State) => Imported p slots yb xb1 s ∧ Imported p slots yb xb2 t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.ready, h.2.1.ready, h.2.2⟩) (fun _ _ h => h)
  have branches : RelCT isa (fun s t => Ranged p slots yb xb1 s ∧ Ranged p slots yb xb2 t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.Domain.ifFlag (VG.Impl.Ffdh.Arm.SharedCheckPrivate.tail
        (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) (VG.Impl.Ffdh.Arm.Domain.ret 0))
      (fun _ _ => True) := by
    apply ifFlag_pair_ct (decide (1 < Spec.Rsa.os2ip yb ∧ Spec.Rsa.os2ip yb < p.P - 1))
      (fun _ h => by simpa only [decide_eq_true_eq] using h.flag)
      (fun _ h => by simpa only [decide_eq_true_eq] using h.flag)
      (fun _ _ h mem rest => h.after_mem mem rest) (fun _ _ h mem rest => h.after_mem mem rest)
    · intro _
      exact (tail_ct backend stable h28 h32 h36 h40 h44 h56 h60 peerLength positive fits count length odd).mono
        (fun _ _ h => ⟨h.1.toReady, h.2.1.toReady, h.2.2⟩) (fun _ _ h => h)
    · intro _
      exact (ret_ct 0).mono (fun _ _ _ => trivial) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.SharedCheckPrivate.publicCheck
  exact relCT_chain imports (fun s h => import_public s h stable h36 h32 peerLength)
    (fun s h => import_public s h stable h36 h32 peerLength)
    (relCT_chain ranges (fun s h => range_public s h stable odd)
      (fun s h => range_public s h stable odd) branches)

/-- What the checks need of their state after the entry and the modulus's shape. -/
structure MainInput (p : Inputs) (slots : List Nat) (yb xb : List Byte) (s : State) : Prop where
  context : Context p slots s
  value : Octets p.base p.publicValue p.len yb s
  scalar : Octets p.base p.privateValue p.len xb s
  valueStack : Region.Disjoint ⟨State.addr p.publicValue, yb.length⟩ ⟨State.addr s.sp, 72⟩
  scalarStack : Region.Disjoint ⟨State.addr p.privateValue, xb.length⟩ ⟨State.addr s.sp, 72⟩
  calls : CallMemory p xb.length s

/-- `Ready`, with the scalar imported. -/
structure ScalarImported (p : Inputs) (slots : List Nat) (yb xb : List Byte) (s : State) : Prop extends
    Ready p slots yb xb s where
  imported : numAt s.mem (State.addr p.base) p.w 1 = Spec.Rsa.os2ip xb

/-- `Ready`, with the scalar's range in the flag. -/
structure ScalarRanged (p : Inputs) (slots : List Nat) (yb xb : List Byte) (s : State) : Prop extends
    Ready p slots yb xb s where
  flag : s.gpr .r11 = scalarValidFlag p (Spec.Rsa.os2ip xb)

theorem ScalarRanged.after_mem {p : Inputs} {slots : List Nat} {yb xb : List Byte} {s t : State}
    (h : ScalarRanged p slots yb xb s) (mem : t.mem = s.mem) (rest : Rest [] s t) :
    ScalarRanged p slots yb xb t :=
  ⟨h.toReady.after_mem mem rest ((rest.gpr .r0 (by simp)).trans h.context.ptr),
    (rest.gpr .r11 (by simp)).trans h.flag⟩

theorem prepare_ready (backend : MontBackend) (s : State) {p : Inputs} {slots : List Nat} {yb xb : List Byte}
    (h : MainInput p slots yb xb s) (stable : stableSlots slots = true)
    (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h32 : 32 ∈ slots) (peerLength : yb.length = p.k)
    (large : 1 < p.P) (odd : p.P % 2 = 1) :
    WP isa (VG.Impl.Ffdh.Arm.SharedPrepare.prepareAt
      (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) 24) s (Ready p slots yb xb) := by
  refine WP.mono (domainSharedPrepareAt24_ok backend s h.context h.calls.toDomainCallMemory stable
    h0 h24 h32 large odd) ?_
  rintro u ⟨context, ready, modulus, r2, frame, rest⟩
  have sourceSep {src : BitVec 32} {bs : List Byte} (source : Octets p.base src p.len bs s)
      (stack : Region.Disjoint ⟨State.addr src, bs.length⟩ ⟨State.addr s.sp, 72⟩)
      (below : Region.Disjoint ⟨State.addr src, bs.length⟩ (belowA s.sp 48))
      (r : Region) (hr : r ∈ domainPrepareWrites p s) : (⟨State.addr src, bs.length⟩ : Region).Disjoint r := by
    simp only [domainPrepareWrites, prepareAtWrites, prepareWrites, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl) | rfl
    · exact source.separate
    · exact stack.sub_right (Offset.sub_base _ (by decide))
    · exact stack.sub_right (Offset.sub_base _ (by decide))
    · exact below
  exact ⟨context, ready, modulus, r2,
    h.value.after_frame frame rest (sourceSep h.value h.valueStack (by rw [peerLength]; exact h.calls.publicValue)),
    h.scalar.after_frame frame rest (sourceSep h.scalar h.scalarStack h.calls.scalarBelow), h.calls.after rest⟩

theorem import_scalar (s : State) {p : Inputs} {slots : List Nat} {yb xb : List Byte}
    (h : Ready p slots yb xb s) (stable : stableSlots slots = true) (h40 : 40 ∈ slots) (h44 : 44 ∈ slots)
    (positive : 0 < xb.length) (length : xb.length ≤ p.k) (count : p.slotValue 44 = BitVec.ofNat 32 xb.length) :
    WP isa (VG.Impl.Ffdh.Arm.Domain.importAt 1 40 44) s (ScalarImported p slots yb xb) := by
  have op0 : Operand 0 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  refine WP.mono (importAt_ok s 1 40 44 h.context stable h40 h44 h.ready (by decide) (by decide) h.scalar
    positive (Nat.le_trans length p.width.2.2.2.1) count) ?_
  rintro u ⟨context, ready, value, keeps, frame, rest⟩
  have fits : arrAt p.w 8 ≤ 8 * p.len := ready.width ▸ ready.layout.2.2.1
  exact ⟨⟨context, ready, (keeps_array_num keeps fits op0 (by decide)).trans h.modulus,
    (keeps_array_num keeps fits op4 (by decide)).trans h.r2,
    h.value.after_workspace frame rest, h.scalar.after_workspace frame rest, h.calls.after rest⟩, value⟩

theorem range_scalar (s : State) {p : Inputs} {slots : List Nat} {yb xb : List Byte}
    (h : ScalarImported p slots yb xb s) (stable : stableSlots slots = true)
    (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) (h60 : 60 ∈ slots) (odd : p.P % 2 = 1) :
    WP isa VG.Impl.Ffdh.Arm.Domain.CheckPrivate.scalarRange s (ScalarRanged p slots yb xb) := by
  refine WP.mono (scalarRange_ok s h.context stable h28 h32 h60 h.ready h.modulus odd) ?_
  rintro u ⟨context, ready, flag, arrays, frame, rest⟩
  rw [h.imported] at flag
  exact ⟨⟨context, ready, (arrays 0 (by simp)).trans h.modulus, (arrays 4 (by simp)).trans h.r2,
    h.value.after_workspace frame rest, h.scalar.after_workspace frame rest, h.calls.after rest⟩, flag⟩

theorem main_ct (backend : MontBackend) {p : Inputs} {slots : List Nat} {yb xb1 xb2 : List Byte}
    (stable : stableSlots slots = true) (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots)
    (h32 : 32 ∈ slots) (h36 : 36 ∈ slots) (h40 : 40 ∈ slots) (h44 : 44 ∈ slots) (h56 : 56 ∈ slots) (h60 : 60 ∈ slots)
    (peerLength : yb.length = p.k) (positive : 0 < xb1.length) (scalarLength : xb1.length ≤ p.k)
    (count : p.slotValue 44 = BitVec.ofNat 32 xb1.length) (length : xb1.length = xb2.length)
    (classification : (0 < Spec.Rsa.os2ip xb1 ∧ Spec.Rsa.os2ip xb1 < scalarBound p) ↔
      (0 < Spec.Rsa.os2ip xb2 ∧ Spec.Rsa.os2ip xb2 < scalarBound p))
    (large : 1 < p.P) (odd : p.P % 2 = 1) :
    RelCT isa (fun s t => MainInput p slots yb xb1 s ∧ MainInput p slots yb xb2 t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.SharedCheckPrivate.main
        (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) (fun _ _ => True) := by
  have prepare := (domainSharedPrepareAt24_ct backend stable h0 h24 h32 large odd).mono
    (P' := fun (s t : State) => MainInput p slots yb xb1 s ∧ MainInput p slots yb xb2 t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨⟨h.1.context, h.1.calls.toDomainCallMemory⟩,
      ⟨h.2.1.context, h.2.1.calls.toDomainCallMemory⟩, h.2.2⟩) (fun _ _ h => h)
  have imports := (importAt_ct (p := p) (a := 1) (slot := 40) (k := xb1.length)
    stable h40 h44 count (by decide)).mono
    (P' := fun (s t : State) => Ready p slots yb xb1 s ∧ Ready p slots yb xb2 t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨⟨h.1.context, h.1.ready⟩, ⟨h.2.1.context, h.2.1.ready⟩, h.2.2⟩) (fun _ _ h => h)
  have ranges := (scalarRange_ct stable h28 h32 h60 odd).mono
    (P' := fun (s t : State) => ScalarImported p slots yb xb1 s ∧ ScalarImported p slots yb xb2 t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨⟨h.1.context, h.1.ready, h.1.modulus⟩, ⟨h.2.1.context, h.2.1.ready, h.2.1.modulus⟩, h.2.2⟩)
    (fun _ _ h => h)
  have branches : RelCT isa (fun s t => ScalarRanged p slots yb xb1 s ∧ ScalarRanged p slots yb xb2 t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.Domain.ifFlag (VG.Impl.Ffdh.Arm.SharedCheckPrivate.publicCheck
        (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) (VG.Impl.Ffdh.Arm.Domain.ret 2))
      (fun _ _ => True) := by
    apply ifFlag_pair_ct (decide (0 < Spec.Rsa.os2ip xb1 ∧ Spec.Rsa.os2ip xb1 < scalarBound p))
      (fun _ h => by simpa only [scalarValidFlag, decide_eq_true_eq] using h.flag)
      (fun _ h => by simpa only [scalarValidFlag, decide_eq_true_eq, ← classification] using h.flag)
      (fun _ _ h mem rest => h.after_mem mem rest) (fun _ _ h mem rest => h.after_mem mem rest)
    · intro _
      exact (public_ct backend stable h28 h32 h36 h40 h44 h56 h60 peerLength positive
        (by have := p.maxLength; omega_using [scalarLength, this]) count length odd).mono
        (fun _ _ h => ⟨h.1.toReady, h.2.1.toReady, h.2.2⟩) (fun _ _ h => h)
    · intro _
      exact (ret_ct 2).mono (fun _ _ _ => trivial) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.SharedCheckPrivate.main
  exact relCT_chain prepare (fun s h => prepare_ready backend s h stable h0 h24 h32 peerLength large odd)
    (fun s h => prepare_ready backend s h stable h0 h24 h32 peerLength large odd)
    (relCT_chain imports (fun s h => import_scalar s h stable h40 h44 positive scalarLength count)
      (fun s h => import_scalar s h stable h40 h44 (by rw [← length]; exact positive)
        (by rw [← length]; exact scalarLength) (by rw [← length]; exact count))
      (relCT_chain ranges (fun s h => range_scalar s h stable h28 h32 h60 odd)
        (fun s h => range_scalar s h stable h28 h32 h60 odd) branches))

theorem entry_ct : RelCT isa (fun s t => s.sp = t.sp)
    (.block VG.Impl.Ffdh.Arm.Domain.CheckPrivate.entry) (fun _ _ => True) := by
  have accesses := RelCT.block_append ((storeLocal_ct .r0 24).seq (RelCT.block_append ((storeLocal_ct .r1 28).seq (RelCT.block_append ((storeLocal_ct .r2 32).seq (RelCT.block_append ((storeLocal_ct .r3 36).seq (RelCT.block_append ((loadLocal_ct .r3 132 (by decide)).seq (RelCT.block_append ((storeLocal_ct .r3 40).seq (RelCT.block_append ((loadLocal_ct .r3 136 (by decide)).seq (RelCT.block_append ((storeLocal_ct .r3 44).seq (RelCT.block_append ((loadLocal_ct .r0 140 (by decide)).seq ((storeLocal_ct .r0 0)))))))))))))))))))
  exact (RelCT.block_append (stackAddr_ct.seq accesses)).mono
    (fun _ _ h => h) (fun _ _ _ => trivial)

theorem body_ct (backend : MontBackend) {p : Inputs} {slots : List Nat} {yb xb1 xb2 : List Byte}
    (stable : stableSlots slots = true) (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots)
    (h32 : 32 ∈ slots) (h36 : 36 ∈ slots) (h40 : 40 ∈ slots) (h44 : 44 ∈ slots)
    (peerLength : yb.length = p.k) (positive : 0 < xb1.length) (scalarLength : xb1.length ≤ p.k)
    (count : p.slotValue 44 = BitVec.ofNat 32 xb1.length) (length : xb1.length = xb2.length)
    (classification : (0 < Spec.Rsa.os2ip xb1 ∧ Spec.Rsa.os2ip xb1 < scalarBound p) ↔
      (0 < Spec.Rsa.os2ip xb2 ∧ Spec.Rsa.os2ip xb2 < scalarBound p)) :
    RelCT isa (fun s t => MainInput p slots yb xb1 s ∧ MainInput p slots yb xb2 t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.Domain.head (VG.Impl.Ffdh.Arm.SharedCheckPrivate.main
        (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul))) (fun _ _ => True) := by
  let Q := fun (xb : List Byte) (s : State) => MainInput p (60 :: 56 :: slots) yb xb s ∧
    s.z = Spec.Rsa.modulusValid p.P p.k
  have head := (head_ct stable h0 h24 h32).mono
    (P' := fun (s t : State) => MainInput p slots yb xb1 s ∧ MainInput p slots yb xb2 t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.context, h.2.1.context, h.2.2⟩) (fun _ _ h => h)
  have wp (s : State) {xb : List Byte} (h : MainInput p slots yb xb s) :
      WP isa (.seq (.block (VG.Impl.Ffdh.Arm.Domain.prepareArgs 24 ++ VG.Impl.Ffdh.Arm.Domain.domainPointers))
        (.block VG.Impl.Bignum.Arm.modulusCheck)) s (Q xb) := by
    refine WP.mono (head_ok s h.context stable h0 h24 h32) ?_
    rintro u ⟨context, zero, frame, rest⟩
    have sourceSep {src : BitVec 32} {bs : List Byte}
        (sep : Region.Disjoint ⟨State.addr src, bs.length⟩ ⟨State.addr s.sp, 72⟩)
        (r : Region) (hr : r ∈ [⟨State.addr s.sp, 72⟩]) : (⟨State.addr src, bs.length⟩ : Region).Disjoint r := by
      rw [List.mem_singleton] at hr; subst r; exact sep
    exact ⟨⟨context, h.value.after_frame frame rest (sourceSep h.valueStack),
      h.scalar.after_frame frame rest (sourceSep h.scalarStack),
      by rw [rest.sp]; exact h.valueStack, by rw [rest.sp]; exact h.scalarStack, h.calls.after rest⟩, zero⟩
  have stable' : stableSlots (60 :: 56 :: slots) = true := by
    change (true && (true && stableSlots slots)) = true
    rw [Bool.true_and, Bool.true_and, stable]
  have branches : RelCT isa (fun s t => Q xb1 s ∧ Q xb2 t ∧ s.sp = t.sp)
      (.ite .eq (VG.Impl.Ffdh.Arm.SharedCheckPrivate.main
        (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) (VG.Impl.Ffdh.Arm.Domain.ret 0))
      (fun _ _ => True) := by
    apply RelCT.ite (fun s t h => by change some s.z = some t.z; rw [h.1.2, h.2.1.2])
    · intro s t tr1 tr2 u v h e1 e2
      have valid : Spec.Rsa.modulusValid p.P p.k = true := by
        have selected := h.2
        change some s.z = some true at selected
        rw [h.1.1.2] at selected
        exact Option.some.inj selected
      have facts := VG.Proof.Bignum.valid_facts valid p.minLength
      exact main_ct backend stable' (by simp [h0]) (by simp [h24]) (by simp [h28])
        (by simp [h32]) (by simp [h36]) (by simp [h40]) (by simp [h44]) (by simp) (by simp)
        peerLength positive scalarLength count length classification facts.2.1 facts.1 s t tr1 tr2 u v
        ⟨h.1.1.1, h.1.2.1.1, h.1.2.2⟩ e1 e2
    · exact (ret_ct 0).mono (fun _ _ _ => trivial) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.Domain.head
  apply RelCT.assoc
  exact relCT_chain head (fun s h => wp s h) (fun s h => wp s h) branches

theorem fn_ct (backend : MontBackend) {p : Inputs} {yb xb1 xb2 : List Byte} (length : xb1.length = xb2.length)
    (classification : (0 < Spec.Rsa.os2ip xb1 ∧ Spec.Rsa.os2ip xb1 < scalarBound p) ↔
      (0 < Spec.Rsa.os2ip xb2 ∧ Spec.Rsa.os2ip xb2 < scalarBound p)) :
    RelCT isa (fun s t => FnInput p yb xb1 s ∧ FnInput p yb xb2 t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.SharedCheckPrivate.code
        (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) (fun _ _ => True) := by
  let P := fun (xb : List Byte) (a : State) => ∃ s, FnInput p yb xb s ∧ a = entered s
  have entry := entry_ct.mono
    (P' := fun (s t : State) => P xb1 s ∧ P xb2 t ∧ s.sp = t.sp)
    (fun _ _ h => h.2.2) (fun _ _ h => h)
  have wp (a : State) {xb : List Byte} (h : P xb a) :
      WP isa (.block VG.Impl.Ffdh.Arm.Domain.CheckPrivate.entry) a
        (MainInput p [0, 44, 40, 36, 32, 28, 24] yb xb) := by
    obtain ⟨s, input, rfl⟩ := h
    refine WP.mono (withAllRest (entry_ok (entered s) input.input.args input.input.incoming input.input.domain
      input.input.domainLength input.input.count input.input.publicValue)) ?_
    rintro u ⟨⟨context, frame⟩, rest⟩
    have sourceSep {src : BitVec 32} {bs : List Byte}
        (sep : Region.Disjoint ⟨State.addr src, bs.length⟩ ⟨State.addr (entered s).sp, 72⟩)
        (r : Region) (hr : r ∈ [⟨State.addr (entered s).sp, 72⟩]) : (⟨State.addr src, bs.length⟩ : Region).Disjoint r := by
      rw [List.mem_singleton] at hr; subst r; exact sep
    exact ⟨context, input.input.value.after_frame frame rest (sourceSep input.input.valueStack),
      input.input.scalar.after_frame frame rest (sourceSep input.input.scalarStack),
      by rw [rest.sp]; exact input.input.valueStack, by rw [rest.sp]; exact input.input.scalarStack,
      input.calls.after rest⟩
  unfold VG.Impl.Ffdh.Arm.SharedCheckPrivate.code
  apply framed_ct (fun _ _ h => ⟨h.1.input.stackFits, h.2.1.input.stackFits⟩) (fun _ _ h => h.2.2)
  intro a b tr1 tr2 u v h e1 e2
  obtain ⟨s, t, related, rfl, rfl⟩ := h
  have body := relCT_chain entry (fun a h => wp a h) (fun a h => wp a h)
    (body_ct backend (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      related.1.input.length related.1.input.positive related.1.input.scalarLength related.1.input.scalarCount
      length classification)
  exact body _ _ _ _ _ _ ⟨⟨s, related.1, rfl⟩, ⟨t, related.2.1, rfl⟩,
    by rw [entered_sp, entered_sp, related.2.2]⟩ e1 e2

theorem contract_ct (backend : MontBackend) : ConstantTime isa (Spec.Ffdh.checkPrivateContract abi 176).pre
    (Spec.Ffdh.checkPrivateContract abi 176).pub (code backend) := by
  intro s t tr1 tr2 u v hs ht hp e1 e2
  obtain ⟨p, yb, xb, base, domain, peer, scalar, count, capacity, privateCount,
    domainBytes, peerBytes, scalarBytes, inputS⟩ := data s hs
  have peerLength (a : State) (h : (Spec.Ffdh.checkPrivateContract abi 176).pre a) :
      (stackArg a 0).toNat = (a.gpr .r2).toNat := by
    sig_pre [Spec.Ffdh.checkPrivateContract, Spec.Ffdh.checkPrivateSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at h
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, length, _, _, _⟩ := h
    exact length
  sig_pub [Spec.Ffdh.checkPrivateContract, Spec.Ffdh.checkPrivateSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at hp
  obtain ⟨sp, bytes, p0, p1, p2, p3, _, p5, p6, p7, p8⟩ := hp
  rw [peerLength s hs, peerLength t ht, ← p0, ← p1, ← p2, ← p3, ← p5, ← p6] at bytes
  simp only [List.append_assoc] at bytes
  obtain ⟨domEqNat, tailEq⟩ := List.append_inj bytes
    (by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range])
  obtain ⟨peerEqNat, statusEq⟩ := List.append_inj tailEq
    (by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range])
  have recover {a b : List Byte} (h : a.map BitVec.toNat = b.map BitVec.toNat) : a = b := by
    have eq := congrArg (List.map (BitVec.ofNat 8)) h
    simpa only [List.map_map, Function.comp_def, BitVec.ofNat_toNat,
      BitVec.setWidth_eq, List.map_id'] using eq
  have domEq := recover domEqNat
  have peerEq := recover peerEqNat
  let xb2 := Spec.Rsa.bytesAt t.mem (State.addr p.privateValue) p.privateLength
  have inputT := input t ht (p := p) (yb := yb) (xb := xb2)
    (p7.symm.trans base) (p0.symm.trans domain) (p3.symm.trans peer) (p5.symm.trans scalar)
    (by rw [← p2]; exact count) (by rw [← p8]; exact capacity) (by rw [← p6]; exact privateCount) ?_ ?_ rfl
  · have xLength : xb.length = p.privateLength := by
      have eq := congrArg List.length scalarBytes
      simpa only [VG.Proof.Bignum.bytesAt_length] using eq.symm
    have x2Length : xb2.length = p.privateLength := VG.Proof.Bignum.bytesAt_length _ _ _
    have status := (List.cons.inj statusEq).1
    rw [← domEq, ← peerEq] at status
    simp only [State.addr] at domainBytes peerBytes scalarBytes
    simp only [count, domain, peer, scalar, privateCount, domainBytes, peerBytes, scalarBytes] at status
    have classification := privateScalarClass_same p (Spec.Rsa.os2ip yb) (Spec.Rsa.os2ip xb) (Spec.Rsa.os2ip xb2) status
    exact (fn_ct backend (by rw [xLength, x2Length]) classification s t tr1 tr2 u v ⟨inputS, inputT, sp⟩ e1 e2).1
  · rw [← p1, ← domain]
    change Spec.Rsa.bytesAt t.mem (BitVec.setWidth 64 (s.gpr .r0)) (s.gpr .r1).toNat = p.dom
    rw [← domEq, domain]
    exact domainBytes
  · rw [← peer, ← count]
    change Spec.Rsa.bytesAt t.mem (BitVec.setWidth 64 (s.gpr .r3)) (s.gpr .r2).toNat = yb
    rw [← peerEq, peer, count]
    exact peerBytes

/-! ## Satisfiable, and verified -/

private def privateSat : State where
  gpr r := match r with | .r0 => 0x1000 | .r1 => 128 | .r2 => 64 | .r3 => 0x2000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8000 then 64 else if a = 0x8005 then 0x21 else if a = 0x8008 then 1 else
    if a = 0x800d then 0x30 else if a = 0x8010 then 0x20 else if a = 0x8011 then 4 else 0
  rd := [⟨0x1000, 128⟩, ⟨0x2000, 64⟩, ⟨0x2100, 1⟩, ⟨0x8000, 20⟩]
  wr := [⟨0x3000, 8448⟩]

theorem sat : ∃ s, (Spec.Ffdh.checkPrivateContract abi 176).pre s := by
  sig_implies_sat [Spec.Ffdh.checkPrivateContract, Spec.Ffdh.checkPrivateSig, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid, abi, argRegs, reduceClassify, Loc.val, State.addr]
    [privateSat, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.Rsa.scratchWords] using privateSat

theorem verified (backend : MontBackend) :
    Verified target (code backend) (Spec.Ffdh.checkPrivateContract abi 176) :=
  ⟨correct backend, contract_ct backend, sat⟩

/-- The code with the product's rewriting of its callers. -/
def calledCode (b : MontBackend) : Prog isa := b.caller.code (code b)

theorem called_verified (b : MontBackend) :
    Verified target (calledCode b) (Spec.Ffdh.checkPrivateContract abi 176) :=
  b.caller.verified (verified b)

end VG.Proof.Ffdh.Arm.SharedCheckPrivate
