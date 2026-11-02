module

public import VerifiedGarbage.Impl.Bignum.Arm.CrtDifference
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.Proof.Bignum.Arm.ReduceOperand
import VerifiedGarbage.Proof.Bignum.Arm.SubModArray
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Impl.Bignum.Arm.R2

/-! # Exact residue subtraction for CRT recombination -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt
open VG.Proof.Rsa.Mont (numAt arrAt Operand)
open VG.Proof.X25519.Arm (Rest)

structure CrtDifferenceInput (base : BitVec 32) (len w M : Nat) (s : State) : Prop where
  ready : ArithmeticReady base len w s
  modulus : numAt s.mem (State.addr base) w 0 = M
  odd : M % 2 = 1
  r2 : numAt s.mem (State.addr base) w 4 = 2 ^ (128 * w) % M
  one : numAt s.mem (State.addr base) w 7 = 1
  bound : numAt s.mem (State.addr base) w 6 < M

theorem crt_difference_ok (s : State) {base : BitVec 32} {len w M : Nat}
    (h : CrtDifferenceInput base len w M s) :
    WP isa difference s fun t => ArithmeticReady base len w t ∧
      numAt t.mem (State.addr base) w 5 =
        (numAt s.mem (State.addr base) w 6 + M - numAt s.mem (State.addr base) w 1 % M) % M ∧
      numAt t.mem (State.addr base) w 0 = M ∧
      numAt t.mem (State.addr base) w 4 = 2 ^ (128 * w) % M ∧ numAt t.mem (State.addr base) w 7 = 1 ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have op (q : Nat) (hq : q = 0 ∨ q = 1 ∨ q = 4 ∨ q = 5 ∨ q = 6 ∨ q = 7) : Operand q := by
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have fits : arrAt w 8 ≤ 8 * len := h.ready.width ▸ h.ready.layout.2.2.1
  have positive : 0 < M := by have := h.ready.modulus; rw [h.modulus] at this; omega
  rw [difference, WP.seq_iff]
  refine WP.mono (reduceOperand_ok s h.ready (op 1 (by decide)) (by decide) (by decide) h.modulus h.odd h.r2 h.one) ?_
  rintro u ⟨readyU, modU, reduced, keepsU, frameU, restU⟩
  have first := keeps_array_num keepsU fits (op 6 (by decide)) (by decide)
  have r2U := (keeps_array_num keepsU fits (op 4 (by decide)) (by decide)).trans h.r2
  have oneU := (keeps_array_num keepsU fits (op 7 (by decide)) (by decide)).trans h.one
  refine WP.mono (subModArray_ok u readyU (op 5 (by decide)) (op 6 (by decide)) (op 1 (by decide))
    (by decide) (by decide) (by decide) (by rw [first, modU]; exact h.bound)
    (by rw [reduced, modU]; exact Nat.mod_lt _ positive)) ?_
  rintro t ⟨readyT, value, keepsT, frameT, restT⟩
  rw [first, modU, reduced] at value
  exact ⟨readyT, value, (keeps_array_num keepsT fits (op 0 (by decide)) (by decide)).trans modU,
    (keeps_array_num keepsT fits (op 4 (by decide)) (by decide)).trans r2U,
    (keeps_array_num keepsT fits (op 7 (by decide)) (by decide)).trans oneU,
    frameU.trans frameT, restU.trans restT⟩

end VG.Proof.Bignum.Arm
