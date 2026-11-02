module

public import VerifiedGarbage.Impl.Bignum.Arm.Exp
public import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpState
import VerifiedGarbage.Proof.Bignum.Arm.MontOp
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Block

/-! # Initialize both Montgomery values used by binary RSA exponentiation -/

@[expose] public section

namespace VG.Proof.Bignum.Arm.ConditionalExp

variable {ok : Prop}
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt arrAt Operand)
open VG.Proof.X25519.Arm (Rest)

theorem expInit_ok (s : State) {base : BitVec 32} {len w M x : Nat}
    (h : ArithmeticReady base len w s) (modulus : numAt s.mem (State.addr base) w 0 = M)
    (odd : M % 2 = 1) (input : numAt s.mem (State.addr base) w 1 = x)
    (r2bound : numAt s.mem (State.addr base) w 4 < M)
    (r2value : ok → numAt s.mem (State.addr base) w 4 % M = 2 ^ (64 * w) * 2 ^ (64 * w) % M) :
    WP isa expInit s fun t => ExpState ok base len w M x 0 t ∧
      (∀ d, d + 4 ≤ 256 → t.mem.readW (VG.Proof.Mont.off (State.addr base) d) 32 =
        s.mem.readW (VG.Proof.Mont.off (State.addr base) d) 32) ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have op (q : Nat) (hq : q = 1 ∨ q = 4 ∨ q = 5 ∨ q = 6 ∨ q = 7) : Operand q := by
    rcases hq with rfl | rfl | rfl | rfl | rfl <;> simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have size : 256 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega
  have coprime := coprime_pow2 odd (64 * w)
  rw [expInit, WP.seq_iff]
  refine WP.mono (smallConst_ok s (1 : BitVec 32) h (o := 7) (by decide) (by decide) (by decide) (by decide)) ?_
  rintro u ⟨readyU, oneU, _, keepsU, frameU, restU⟩
  change numAt u.mem (State.addr base) w 7 = 1 at oneU
  have modU := (h.after_array (by decide) keepsU frameU restU readyU.ptr).2.trans modulus
  have inputU := (keeps_array_num keepsU fits (op 1 (by decide)) (by decide)).trans input
  have r2U := keeps_array_num keepsU fits (op 4 (by decide)) (by decide)
  rw [WP.seq_iff]
  refine WP.mono (montOp_ok u readyU (op 6 (by decide)) (op 4 (by decide)) (op 7 (by decide)) (by decide)
    (by rw [oneU]; exact readyU.modulus)) ?_
  rintro v ⟨readyV, modV, boundV, valueV, keepsV, frameV, restV⟩
  rw [modU] at modV boundV valueV
  rw [oneU, Nat.mul_one, r2U] at valueV
  have powerV (ho : ok) := mont_cancel coprime (valueV.trans (r2value ho))
  have oneV := (keeps_array_num keepsV fits (op 7 (by decide)) (by decide)).trans oneU
  have inputV := (keeps_array_num keepsV fits (op 1 (by decide)) (by decide)).trans inputU
  have r2V := (keeps_array_num keepsV fits (op 4 (by decide)) (by decide)).trans r2U
  refine WP.mono (montOp_ok v readyV (op 5 (by decide)) (op 1 (by decide)) (op 4 (by decide)) (by decide)
    (by rw [modV, r2V]; exact r2bound)) ?_
  rintro t ⟨readyT, modT, boundT, valueT, keepsT, frameT, restT⟩
  rw [modV] at modT boundT valueT
  rw [inputV, r2V] at valueT
  have encoded : ok → numAt t.mem (State.addr base) w 5 % M = x * 2 ^ (64 * w) % M := by
    intro ho
    apply mont_cancel coprime
    rw [valueT, Nat.mul_mod, r2value ho, ← Nat.mul_mod, Nat.mul_assoc]
  have powerT := keeps_array_num keepsT fits (op 6 (by decide)) (by decide)
  have oneT := (keeps_array_num keepsT fits (op 7 (by decide)) (by decide)).trans oneV
  have r2T := (keeps_array_num keepsT fits (op 4 (by decide)) (by decide)).trans r2V
  have r2Exact : ok → numAt s.mem (State.addr base) w 4 = 2 ^ (128 * w) % M := by
    intro ho
    have rv := r2value ho
    rw [Nat.mod_eq_of_lt r2bound, ← Nat.pow_add,
      show 64 * w + 64 * w = 128 * w by omega] at rv
    exact rv
  refine ⟨⟨readyT, modT, coprime, boundT, encoded, ?_, ?_, oneT, fun ho => r2T.trans (r2Exact ho)⟩, ?_,
    frameU.trans (frameV.trans frameT), restU.trans (restV.trans restT)⟩
  · rw [powerT]; exact boundV
  · intro ho
    rw [powerT, Nat.pow_zero, Nat.one_mul]; exact powerV ho
  · intro d hd
    rw [keeps_header_readW keepsT size (d := d) (bits := 32) hd,
      keeps_header_readW keepsV size (d := d) (bits := 32) hd,
      keeps_header_readW keepsU size (d := d) (bits := 32) hd]

end VG.Proof.Bignum.Arm.ConditionalExp
