module

import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicSpec
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.Math
public import VerifiedGarbage.Proof.Ffdh.Arm.Context
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
import VerifiedGarbage.Proof.Ffdh.Arm.Subgroup
import VerifiedGarbage.Proof.Ffdh.Arm.Branch
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareAt
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
import VerifiedGarbage.Proof.Ffdh.Arm.QTest
import VerifiedGarbage.Proof.Ffdh.Arm.ImportAt
import VerifiedGarbage.Proof.Ffdh.Arm.Range
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ffdh.Arm.Head
public import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicBody
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Impl.Ffdh.Arm.Checks
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.Proof.Ffdh.Arm.CheckFlag
import VerifiedGarbage.Proof.Ffdh.Arm.ValueChecks
import VerifiedGarbage.Proof.Bignum.Arm.ReduceOperand
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.PdParity
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! ### `Ffdh.Arm.DomainBody`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.Odd`, which this module and modules that import it used -/

section

/-! Parity comes from the operand's least significant byte. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt)
open VG.Proof.X25519.Arm (Rest wp_ldr wp_ldrb wp_dp op2_imm dpVal)

theorem odd_ok (s : State) {base : BitVec 32} {len w a : Nat}
    (h : ArithmeticReady base len w s) (ha : a < 8) :
    WP isa (VG.Impl.Ffdh.Arm.odd a) s fun t => ArithmeticReady base len w t ∧
      t.gpr .r11 = BitVec.ofNat 32 (numAt s.mem (State.addr base) w a % 2) ∧
      t.mem = s.mem ∧ Rest [.r4, .r11] s t := by
  have hw : 2 ≤ w := h.width ▸ h.layout.1
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have bound := array_end_le (w := w) ha
  have size : 64 + 8 * a + 4 ≤ 8 * len := by
    simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits
    omega_using [ha, fits]
  have header := nativeHeader_of_layout s.mem base h.workspace.nowrap (Nat.le_refl _) h.layout
  rw [h.width] at header
  have ptrAddr : State.addr (base + BitVec.ofNat 32 (arrAt w a)) = off (State.addr base) (arrAt w a) :=
    VG.Arm.addr_add (by have := h.workspace.nowrap; omega_using [fits, bound, this])
  unfold VG.Impl.Ffdh.Arm.odd
  refine wp_ldr (a := off (State.addr base) (64 + 8 * a)) (by omega_using [ha])
    (by rw [h.ptr]; exact addr_add (by have := h.workspace.nowrap; omega_using [size, this]))
    (h.workspace.read size) fun u loaded => ?_
  have ptrU : u.gpr .r4 = base + BitVec.ofNat 32 (arrAt w a) := loaded.gpr.trans (header.array a ha)
  have read : InRegions (u.rd ++ u.wr) (off (State.addr base) (arrAt w a)) 1 := by
    rw [loaded.rd, loaded.wr]
    refine ⟨⟨State.addr base, 8 * len⟩, List.mem_append_right _ h.workspace.writable, ?_⟩
    exact Offset.contains_base _ (by omega_using [fits, bound]) (by have := h.workspace.nowrap; omega_using [fits, bound, this])
  refine wp_ldrb (a := off (State.addr base) (arrAt w a)) (by decide)
    (by rw [ptrU, BitVec.add_zero, ptrAddr]) read fun v byte => ?_
  refine wp_dp (op2_imm (by decide : encodable (1 : BitVec 32) = true)) fun t masked => WP.block_nil ?_
  have rest : Rest [.r4, .r11] s t := (loaded.rest (by simp)).trans ((byte.rest (by simp)).trans (masked.rest (by simp)))
  have mem : t.mem = s.mem := masked.mem.trans (byte.mem.trans loaded.mem)
  refine ⟨h.of_mem mem rest ((rest.gpr .r0 (by simp)).trans h.ptr), ?_, mem, rest⟩
  rw [masked.gpr, dpVal, byte.gpr, loaded.mem]
  exact numAt_parity_word s.mem (State.addr base) (by omega_using [hw])

end VG.Proof.Ffdh.Arm

end

end

/-! ### `Ffdh.Arm.DomainDivides`, which this module and modules that import it used -/

section

/-! Divisibility is checked by reducing the full-width p modulo q. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt Operand arrAt)

theorem domainDivides_ok (s : State) {p : Inputs} {slots : List Nat}
    (h : Context p slots s) (stable : stableSlots slots = true)
    (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h32 : 32 ∈ slots) (h60 : 60 ∈ slots)
    (hasQ : p.hasQ = true) (large : 1 < p.Q) (odd : p.Q % 2 = 1) :
    WP isa VG.Impl.Ffdh.Arm.Domain.CheckDomain.divides s fun t => Context p slots t ∧
      t.gpr .r11 = (if p.P % p.Q = 1 then 1 else 0) ∧
      Frame (prepareAtWrites p s) s.mem t.mem ∧ VG.Proof.X25519.Arm.Rest roundClobbers s t := by
  have op0 : Operand 0 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op1 : Operand 1 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op7 : Operand 7 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have qStack : Region.Disjoint ⟨State.addr p.q, p.k⟩ ⟨State.addr s.sp, 72⟩ :=
    h.toArgumentMemory.domainSliceStack (by have := p.minLength; omega_using [this])
      (by rw [p.domainLength, hasQ]; simp only [ite_true]; omega_using [])
  rw [VG.Impl.Ffdh.Arm.Domain.CheckDomain.divides, WP.seq_iff]
  refine WP.mono (prepareAt_ok s 60 h stable h60 h32 h0 (h.qBytes hasQ) (p.qLength hasQ) qStack large odd) ?_
  rintro u ⟨contextU, readyU, modU, r2U, frameU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (importAt_ok u 1 24 32 contextU stable h24 h32 readyU (by decide) (by decide) contextU.pBytes
    (by rw [p.pLength]; have := p.minLength; omega_using [this]) (by rw [p.pLength]; exact p.width.2.2.2.1)
    (by change BitVec.ofNat 32 p.k = _; rw [p.pLength])) ?_
  rintro v ⟨_, readyV, valueV, keepsV, frameV, restV⟩
  have fits : arrAt p.w 8 ≤ 8 * p.len := readyV.width ▸ readyV.layout.2.2.1
  have modV := (keeps_array_num keepsV fits op0 (by decide)).trans modU
  have r2V := (keeps_array_num keepsV fits op4 (by decide)).trans r2U
  rw [WP.seq_iff]
  refine WP.mono (smallConst_ok v 1 readyV (by decide : 7 < 8) (by decide) (by decide) (by decide)) ?_
  rintro w ⟨readyW, one, _, keepsW, frameW, restW⟩
  have modW := (keeps_array_num keepsW fits op0 (by decide)).trans modV
  have r2W := (keeps_array_num keepsW fits op4 (by decide)).trans r2V
  rw [WP.seq_iff]
  refine WP.mono (reduceOperand_ok w readyW op1 (by decide) (by decide) modW odd r2W one) ?_
  rintro x ⟨readyX, _, reduced, _, frameX, restX⟩
  rw [keeps_array_num keepsW fits op1 (by decide), valueV] at reduced
  refine WP.mono (isOne_ok x readyX op1 (by decide)) ?_
  rintro t ⟨readyT, flag, _, frameT, restT⟩
  rw [reduced] at flag
  have frame : Frame (prepareAtWrites p s) s.mem t.mem := by
    have work := ((frameV.trans frameW).trans frameX).trans frameT
    exact frameU.trans (work.mono (by intro r hr; rw [List.mem_singleton] at hr; subst r; exact List.mem_cons_self))
  have rest := (((restU.trans restV).trans restW).trans restX).trans restT
  have contextT : Context p slots t := by
    have frameWork := ((frameV.trans frameW).trans frameX).trans frameT
    exact contextU.after_workspace frameWork (((restV.trans restW).trans restX).trans restT) readyT.ptr
      (fun d hd => (stableSlots_at stable hd).1)
  exact ⟨contextT, flag, frame, rest⟩

end VG.Proof.Ffdh.Arm

end

end

/-! ### `Ffdh.Arm.DomainQRange`, which this module and modules that import it used -/

section

/-! The subgroup order must be odd and strictly inside the modulus range. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt Operand arrAt)

def qRangeFlag (p : Inputs) : BitVec 32 := if 2 < p.Q ∧ p.Q < p.P - 1 ∧ p.Q % 2 = 1 then 1 else 0

theorem qRange_ok (s : State) {p : Inputs} {slots : List Nat}
    (h : Context p slots s) (stable : stableSlots slots = true) (h60 : 60 ∈ slots) (h32 : 32 ∈ slots)
    (hasQ : p.hasQ = true) (ready : ArithmeticReady p.base p.len p.w s)
    (modulus : numAt s.mem (State.addr p.base) p.w 0 = p.P) (odd : p.P % 2 = 1)
    (r2 : numAt s.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P) :
    WP isa VG.Impl.Ffdh.Arm.Domain.CheckDomain.qRange s fun t => Context p slots t ∧
      ArithmeticReady p.base p.len p.w t ∧ t.gpr .r11 = qRangeFlag p ∧
      numAt t.mem (State.addr p.base) p.w 0 = p.P ∧
      numAt t.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P ∧
      Frame [⟨State.addr p.base, 8 * p.len⟩] s.mem t.mem ∧ VG.Proof.X25519.Arm.Rest roundClobbers s t := by
  have op0 : Operand 0 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op1 : Operand 1 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have qLength := p.qLength hasQ
  rw [VG.Impl.Ffdh.Arm.Domain.CheckDomain.qRange, WP.seq_iff]
  refine WP.mono (importAt_ok s 1 60 32 h stable h60 h32 ready (by decide) (by decide) (h.qBytes hasQ)
    (by rw [qLength]; have := p.minLength; omega_using [this]) (by rw [qLength]; exact p.width.2.2.2.1)
    (by change BitVec.ofNat 32 p.k = _; rw [qLength])) ?_
  rintro u ⟨_, readyU, q, keepsU, frameU, restU⟩
  have fits : arrAt p.w 8 ≤ 8 * p.len := readyU.width ▸ readyU.layout.2.2.1
  have modU := (keeps_array_num keepsU fits op0 (by decide)).trans modulus
  have r2U := (keeps_array_num keepsU fits op4 (by decide)).trans r2
  rw [WP.seq_iff]
  refine WP.mono (inRange_ok u readyU op1 (by decide) (by rw [modU]; exact odd)) ?_
  rintro v ⟨readyV, range, arraysV, frameV, restV⟩
  rw [q, modU] at range
  rw [WP.seq_iff]
  refine WP.mono (saveFlag_ok v readyV) ?_
  rintro w ⟨readyW, saved, arraysW, frameW, restW⟩
  rw [WP.seq_iff]
  refine WP.mono (odd_ok w readyW (by decide : 1 < 8)) ?_
  rintro x ⟨readyX, parity, memX, restX⟩
  rw [arraysW 1 (by decide), arraysV 1 op1 (by decide), q] at parity
  refine WP.mono (andFlag_ok x readyX) ?_
  rintro t ⟨⟨flag, memT⟩, restT⟩
  have readyT := readyX.of_mem memT restT ((restT.gpr .r0 (by simp)).trans readyX.ptr)
  have frame : Frame [⟨State.addr p.base, 8 * p.len⟩] s.mem t.mem := by
    rw [memT, memX]; exact (frameU.trans frameV).trans frameW
  have rest : VG.Proof.X25519.Arm.Rest roundClobbers s t :=
    (((restU.trans restV).trans (restW.mono (by simp [roundClobbers]))).trans
      (restX.mono (by simp [roundClobbers]))).trans (restT.mono (by simp [roundClobbers]))
  refine ⟨h.after_workspace frame rest readyT.ptr (fun d hd => (stableSlots_at stable hd).1), readyT, ?_, ?_, ?_, frame, rest⟩
  · rw [flag, parity, memX, saved, range]
    change BitVec.ofNat 32 (p.Q % 2) &&& (if 1 < p.Q ∧ p.Q < p.P - 1 then 1 else 0) = qRangeFlag p
    have small : p.Q % 2 = 0 ∨ p.Q % 2 = 1 := by omega_using []
    rcases small with even | oddQ
    · simp [even, qRangeFlag]
    · rw [oddQ]
      by_cases lower : 1 < p.Q <;> by_cases upper : p.Q < p.P - 1 <;>
        simp [qRangeFlag, lower, upper, oddQ, show (2 < p.Q ↔ 1 < p.Q) by omega_using [oddQ]]
  · rw [memT, memX, arraysW 0 (by decide), arraysV 0 op0 (by decide)]
    exact modU
  · rw [memT, memX, arraysW 4 (by decide), arraysV 4 op4 (by decide)]
    exact r2U

end VG.Proof.Ffdh.Arm

end

end

/-! ### `Ffdh.Arm.DomainMain`, which only this module used -/

section

/-! ### `Ffdh.Arm.DomainTail`, which only this module used -/

section

/-! ### `Ffdh.Arm.DomainQChecks`, which only this module used -/

section

/-! Native subgroup-order validation, divisibility, and generator subgroup membership. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)

def domainQFlag (p : Inputs) : BitVec 32 :=
  if 2 < p.Q ∧ p.Q < p.P - 1 ∧ p.Q % 2 = 1 then
    if p.P % p.Q = 1 then if Spec.Rsa.powMod p.G p.Q p.P = 1 then 1 else 0 else 0 else 0

theorem domainQChecks_ok (s : State) {p : Inputs} {slots : List Nat}
    (h : Context p slots s) (stable : stableSlots slots = true)
    (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h32 : 32 ∈ slots) (h56 : 56 ∈ slots) (h60 : 60 ∈ slots)
    (hasQ : p.hasQ = true) (ready : ArithmeticReady p.base p.len p.w s)
    (modulus : numAt s.mem (State.addr p.base) p.w 0 = p.P) (large : 1 < p.P) (odd : p.P % 2 = 1)
    (r2 : numAt s.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P) :
    WP isa VG.Impl.Ffdh.Arm.Domain.CheckDomain.qChecks s fun t =>
      t.gpr .r0 = domainQFlag p ∧ Frame (prepareAtWrites p s) s.mem t.mem := by
  have extend {m m' : Mem} (f : Frame [⟨State.addr p.base, 8 * p.len⟩] m m') : Frame (prepareAtWrites p s) m m' :=
    f.mono (by intro r hr; rw [List.mem_singleton] at hr; subst r; exact List.mem_cons_self)
  rw [VG.Impl.Ffdh.Arm.Domain.CheckDomain.qChecks, WP.seq_iff]
  refine WP.mono (qRange_ok s h stable h60 h32 hasQ ready modulus odd r2) ?_
  rintro u ⟨contextU, _, flagU, _, _, frameU, restU⟩
  rw [VG.Impl.Ffdh.Arm.Domain.ifFlag, WP.seq_iff]
  refine WP.mono (testFlag_ok u) ?_
  rintro v ⟨⟨zeroV, memV⟩, restV⟩
  by_cases qValid : 2 < p.Q ∧ p.Q < p.P - 1 ∧ p.Q % 2 = 1
  · refine WP.ite true (by change some (!v.z) = some true; rw [zeroV, flagU, qRangeFlag, ite_eq_left qValid]; rfl) ?_ (by intro hf; cases hf)
    intro _
    have contextV := contextU.of_mem memV restV ((restV.gpr .r0 (by simp)).trans contextU.ptr)
    rw [WP.seq_iff]
    refine WP.mono (domainDivides_ok v contextV stable h0 h24 h32 h60 hasQ (by omega_using [qValid]) qValid.2.2) ?_
    rintro w ⟨contextW, dividesW, frameW, restW⟩
    rw [VG.Impl.Ffdh.Arm.Domain.ifFlag, WP.seq_iff]
    refine WP.mono (testFlag_ok w) ?_
    rintro x ⟨⟨zeroX, memX⟩, restX⟩
    by_cases divides : p.P % p.Q = 1
    · refine WP.ite true (by change some (!x.z) = some true; rw [zeroX, dividesW, ite_eq_left divides]; rfl) ?_ (by intro hf; cases hf)
      intro _
      have contextX := contextW.of_mem memX restX ((restX.gpr .r0 (by simp)).trans contextW.ptr)
      have pStack : Region.Disjoint ⟨State.addr p.domain, p.k⟩ ⟨State.addr x.sp, 72⟩ :=
        contextX.domainStack.sub_left (Region.sub_prefix (by rw [p.domainLength]; split <;> omega_using []))
      rw [WP.seq_iff]
      refine WP.mono (prepareAt_ok x 24 contextX stable h24 h32 h0 contextX.pBytes p.pLength pStack large odd) ?_
      rintro y ⟨contextY, readyY, modY, r2Y, frameY, restY⟩
      rw [WP.seq_iff]
      refine WP.mono (subgroup_ok y 56 contextY stable h56 h60 h32 hasQ readyY modY odd r2Y contextY.gBytes p.gLength) ?_
      rintro z ⟨_, _, flagZ, _, _, frameZ, _⟩
      refine WP.mono (finishFlag_ok z) ?_
      rintro t ⟨⟨result, memT⟩, _⟩
      refine ⟨by rw [result, flagZ, domainQFlag, ite_eq_left qValid, ite_eq_left divides]; rfl, ?_⟩
      have frameW' : Frame (prepareAtWrites p s) u.mem w.mem := by
        rw [memV] at frameW
        simpa only [prepareAtWrites, prepareWrites, restV.sp, restW.sp, restU.sp] using frameW
      have frameY' : Frame (prepareAtWrites p s) w.mem y.mem := by
        rw [memX] at frameY
        simpa only [prepareAtWrites, prepareWrites, restX.sp, restW.sp, restV.sp, restU.sp] using frameY
      rw [memT]
      exact (((extend frameU).trans frameW').trans frameY').trans (extend frameZ)
    · refine WP.ite false (by change some (!x.z) = some false; rw [zeroX, dividesW, ite_eq_right divides]; rfl) (by intro ht; cases ht) ?_
      intro _
      refine WP.mono (ret_ok x 0 (by decide)) ?_
      rintro t ⟨⟨result, memT⟩, _⟩
      refine ⟨by rw [result, domainQFlag, ite_eq_left qValid, ite_eq_right divides], ?_⟩
      rw [memT, memX]
      rw [memV] at frameW
      exact (extend frameU).trans (by simpa only [prepareAtWrites, prepareWrites, restV.sp, restU.sp] using frameW)
  · refine WP.ite false (by change some (!v.z) = some false; rw [zeroV, flagU, qRangeFlag, ite_eq_right qValid]; rfl) (by intro ht; cases ht) ?_
    intro _
    refine WP.mono (ret_ok v 0 (by decide)) ?_
    rintro t ⟨⟨result, memT⟩, _⟩
    exact ⟨by rw [result, domainQFlag, ite_eq_right qValid], by rw [memT, memV]; exact extend frameU⟩

end VG.Proof.Ffdh.Arm

end

end


/-! A domain without q needs only the modulus and generator checks; with q,
the order, divisibility, and subgroup checks run in native code. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)

def domainTailFlag (p : Inputs) : BitVec 32 := if p.hasQ = true then domainQFlag p else 1

theorem domainTail_ok (s : State) {p : Inputs} {slots : List Nat}
    (h : Context p slots s) (stable : stableSlots slots = true)
    (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots)
    (h56 : 56 ∈ slots) (h60 : 60 ∈ slots)
    (ready : ArithmeticReady p.base p.len p.w s)
    (modulus : numAt s.mem (State.addr p.base) p.w 0 = p.P) (large : 1 < p.P) (odd : p.P % 2 = 1)
    (r2 : numAt s.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P) :
    WP isa (VG.Impl.Ffdh.Arm.Domain.withQ VG.Impl.Ffdh.Arm.Domain.CheckDomain.qChecks
      (VG.Impl.Ffdh.Arm.Domain.ret 1)) s fun t =>
        t.gpr .r0 = domainTailFlag p ∧ Frame (prepareAtWrites p s) s.mem t.mem := by
  rw [VG.Impl.Ffdh.Arm.Domain.withQ, WP.seq_iff]
  refine WP.mono (qTest_ok s h h28 h32) ?_
  rintro u ⟨⟨zero, memU⟩, restU⟩
  have ptrU := (restU.gpr .r0 (by simp)).trans ready.ptr
  have contextU := h.of_mem memU restU ptrU
  have readyU := ready.of_mem memU restU ptrU
  refine WP.ite p.hasQ (by simp only [eval, zero, Bool.not_not]) ?_ ?_
  · intro hasQ
    refine WP.mono (domainQChecks_ok u contextU stable h0 h24 h32 h56 h60 hasQ readyU
      (by rw [memU]; exact modulus) large odd (by rw [memU]; exact r2)) ?_
    rintro t ⟨result, frame⟩
    refine ⟨by rw [domainTailFlag, ite_eq_left hasQ]; exact result, ?_⟩
    rw [memU] at frame
    simpa only [prepareAtWrites, prepareWrites, restU.sp] using frame
  · intro hasQ
    refine WP.mono (ret_ok u 1 (by decide)) ?_
    rintro t ⟨⟨result, memT⟩, _⟩
    refine ⟨by rw [domainTailFlag, ite_eq_right (by rw [hasQ]; decide)]; exact result, ?_⟩
    rw [memT, memU]; exact Frame.refl _ _

end VG.Proof.Ffdh.Arm

end

end


/-! Native generator range and optional subgroup-order validation. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt Operand arrAt)

def domainMainFlag (p : Inputs) (y : Nat) : BitVec 32 :=
  if 1 < y ∧ y < p.P - 1 then domainTailFlag p else 0

theorem domainMain_ok (s : State) {p : Inputs} {slots : List Nat} {yb : List Byte}
    (h : Context p slots s) (stable : stableSlots slots = true)
    (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots)
    (h56 : 56 ∈ slots) (h60 : 60 ∈ slots)
    (large : 1 < p.P) (odd : p.P % 2 = 1)
    (value : Octets p.base p.g p.len yb s) (length : yb.length = p.k)
    (valueStack : Region.Disjoint ⟨State.addr p.g, yb.length⟩ ⟨State.addr s.sp, 72⟩) :
    WP isa VG.Impl.Ffdh.Arm.Domain.CheckDomain.main s fun t =>
      t.gpr .r0 = domainMainFlag p (Spec.Rsa.os2ip yb) ∧ Frame (prepareAtWrites p s) s.mem t.mem := by
  have op0 : Operand 0 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op1 : Operand 1 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have extend {m m' : Mem} (f : Frame [⟨State.addr p.base, 8 * p.len⟩] m m') : Frame (prepareAtWrites p s) m m' :=
    f.mono (by intro r hr; rw [List.mem_singleton] at hr; subst r; exact List.mem_cons_self)
  have pStack : Region.Disjoint ⟨State.addr p.domain, p.k⟩ ⟨State.addr s.sp, 72⟩ :=
    h.domainStack.sub_left (Region.sub_prefix (by rw [p.domainLength]; split <;> omega_using []))
  rw [VG.Impl.Ffdh.Arm.Domain.CheckDomain.main, WP.seq_iff]
  refine WP.mono (prepareAt_ok s 24 h stable h24 h32 h0 h.pBytes p.pLength pStack large odd) ?_
  rintro u ⟨contextU, readyU, modU, r2U, frameU, restU⟩
  have valueU := value.after_frame frameU restU (by
    intro r hr
    simp only [prepareAtWrites, prepareWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact value.separate
    · exact valueStack.sub_right (Offset.sub_base _ (by decide))
    · exact valueStack.sub_right (Offset.sub_base _ (by decide)))
  rw [WP.seq_iff]
  refine WP.mono (importAt_ok u 1 56 32 contextU stable h56 h32 readyU (by decide) (by decide)
    valueU (by rw [length]; have := p.minLength; omega_using [this]) (by rw [length]; exact p.width.2.2.2.1)
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
    refine WP.mono (domainTail_ok z contextZ stable h0 h24 h28 h32 h56 h60 readyZ
      (by rw [memZ]; exact modW) large odd (by rw [memZ]; exact r2W)) ?_
    rintro t ⟨result, frameT⟩
    refine ⟨?_, ?_⟩
    · rw [domainMainFlag, ite_eq_left valid]; exact result
    · rw [memZ] at frameT
      have frameT' : Frame (prepareAtWrites p s) w.mem t.mem := by
        simpa only [prepareAtWrites, prepareWrites, restZ.sp, restW.sp, restV.sp, restU.sp] using frameT
      exact frameW'.trans frameT'
  · refine WP.ite false (by change some (!z.z) = some false; rw [zero, flag, ite_eq_right valid]; rfl) (by intro ht; cases ht) ?_
    intro _
    refine WP.mono (ret_ok z 0 (by decide)) ?_
    rintro t ⟨⟨result, memT⟩, _⟩
    refine ⟨?_, ?_⟩
    · rw [domainMainFlag, ite_eq_right valid]; exact result
    · rw [memT, memZ]; exact frameW'

end VG.Proof.Ffdh.Arm

end

end


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
      exact contextU.toArgumentMemory.domainSliceStack (by have := p.minLength; omega_using [this])
        (by rw [p.domainLength]; split <;> omega_using [])
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

end

end

/-! Native parameter checks agree with the shared algebraic domain predicate. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG

theorem modOne_iff {p q : Nat} (positive : 0 < p) (large : 1 < q) :
    p % q = 1 ↔ (p - 1) % q = 0 := by
  constructor
  · intro h
    have product : p - 1 = q * (p / q) := by
      have split := Nat.mod_add_div p q
      rw [h] at split
      omega_using [split]
    rw [product, Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod]
  · intro h
    have step : p = (p - 1) + 1 := by omega_using [positive]
    calc
      p % q = ((p - 1) + 1) % q := congrArg (· % q) step
      _ = 1 := by rw [Nat.add_mod, h, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt large]

theorem Inputs.domainG (p : Inputs) : (Spec.Ffdh.domainOf p.k p.dom).g = p.G := rfl

theorem domainValid_native_iff (p : Inputs) : Spec.Ffdh.domainValid p.k p.dom = true ↔
    Spec.Rsa.modulusValid p.P p.k = true ∧ (1 < p.G ∧ p.G < p.P - 1) ∧
      (p.hasQ = true → (2 < p.Q ∧ p.Q < p.P - 1 ∧ p.Q % 2 = 1) ∧
        p.P % p.Q = 1 ∧ Spec.Rsa.powMod p.G p.Q p.P = 1) := by
  rw [VG.Proof.Ffdh.domainValid_iff, p.domainP, p.domainG, p.domainQ]
  by_cases hasQ : p.hasQ = true
  · rw [ite_eq_left hasQ]
    simp only [Option.some.injEq, forall_eq', hasQ, true_implies]
    constructor
    · rintro ⟨modulus, range, ⟨odd, lower, upper⟩, divides, power⟩
      have facts := VG.Proof.Bignum.valid_facts modulus p.minLength
      refine ⟨modulus, range, ⟨by omega_using [odd, lower], upper, odd⟩, (modOne_iff (by omega_using [range]) lower).mpr divides, ?_⟩
      simpa only [VG.Proof.Bignum.powMod_eq] using power
    · rintro ⟨modulus, range, ⟨lower, upper, odd⟩, divides, power⟩
      have facts := VG.Proof.Bignum.valid_facts modulus p.minLength
      refine ⟨modulus, range, ⟨odd, by omega_using [lower], upper⟩, (modOne_iff (by omega_using [range]) (by omega_using [lower])).mp divides, ?_⟩
      simpa only [VG.Proof.Bignum.powMod_eq] using power
  · simp [hasQ]

theorem checkedDomainFlag_spec (p : Inputs) : checkedDomainFlag p =
    if Spec.Ffdh.domainValid p.k p.dom then 1 else 0 := by
  have valid := domainValid_native_iff p
  by_cases modulus : Spec.Rsa.modulusValid p.P p.k = true <;>
    by_cases range : 1 < p.G ∧ p.G < p.P - 1 <;>
    by_cases hasQ : p.hasQ = true <;>
    by_cases qrange : 2 < p.Q ∧ p.Q < p.P - 1 ∧ p.Q % 2 = 1 <;>
    by_cases divides : p.P % p.Q = 1 <;>
    by_cases power : Spec.Rsa.powMod p.G p.Q p.P = 1 <;>
    simp_all [checkedDomainFlag, domainMainFlag, domainTailFlag, domainQFlag]

end VG.Proof.Ffdh.Arm
