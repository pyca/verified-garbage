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

end VG.Proof.Ffdh.Arm

end

end


/-! Full native parameter validation, including a rejected modulus shape. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont

def checkedDomainFlag (p : Inputs) : BitVec 32 :=
  if Spec.Rsa.modulusValid p.P p.k = true then domainMainFlag p p.G else 0

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
