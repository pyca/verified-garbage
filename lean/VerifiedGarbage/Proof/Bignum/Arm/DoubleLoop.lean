module

public import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoopBody
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Repeated doubling computes a power of two modulo the RSA modulus -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Spec.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

theorem double_power_step (i x m : Nat) :
    (2 * (2 ^ i * x % m)) % m = (2 ^ (i + 1) * x) % m := by
  simp only [Nat.pow_succ', Nat.mul_assoc, Nat.mul_mod, Nat.mod_mod]

/-- The loop's trip count is public; its numbers and inverse remain secret. -/
theorem doubleLoop_ok (s : State) {base : BitVec 32} {len w c : Nat}
    (h : DoubleLoopReady base len w c s) (hc : 0 < c) (hc' : c < 2 ^ 32) :
    WP isa doubleLoop s fun t => DoubleLoopReady base len w 0 t ∧
      numAt t.mem (State.addr base) w 4 =
        (2 ^ c * numAt s.mem (State.addr base) w 4) % numAt s.mem (State.addr base) w 0 ∧
      numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  let inv := fun k t => ∃ i, i + k = c ∧ 0 < k ∧ DoubleLoopReady base len w k t ∧
    numAt t.mem (State.addr base) w 4 =
      (2 ^ i * numAt s.mem (State.addr base) w 4) % numAt s.mem (State.addr base) w 0 ∧
    numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 ∧
    Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t
  unfold doubleLoop
  refine WP.loop (M := isa) inv ?_ c s ?_
  · intro k t hi
    obtain ⟨i, hik, hk, ready, number, modulus, frame, rest⟩ := hi
    refine WP.mono (doubleLoopBody_ok t ready hk (by omega)) ?_
    rintro u ⟨next, value, modU, zero, frameU, restU⟩
    have step : numAt u.mem (State.addr base) w 4 =
        (2 ^ (i + 1) * numAt s.mem (State.addr base) w 4) % numAt s.mem (State.addr base) w 0 := by
      rw [value, number, modulus, double_power_step]
    have oldM := modU.trans modulus
    have wholeFrame := frame.trans frameU
    have wholeRest := rest.trans restU
    by_cases exit : k = 1
    · left
      refine ⟨?_, ?_, ?_, oldM, wholeFrame, wholeRest⟩
      · change some (!u.z) = some false
        simp only [zero, exit, decide_true, Bool.not_true]
      · simpa only [exit, Nat.sub_self] using next
      · simpa only [show i + 1 = c by omega] using step
    · right
      refine ⟨?_, k - 1, by omega, i + 1, by omega, by omega, next, step, oldM, wholeFrame, wholeRest⟩
      change some (!u.z) = some true
      simp only [zero, exit, decide_false, Bool.not_false]
  · refine ⟨0, by omega, hc, h, ?_, rfl, Frame.refl _ _, Rest.refl _ _⟩
    simp only [Nat.pow_zero, Nat.one_mul, Nat.mod_eq_of_lt h.operand]

/-- Starting from one, 128*w doublings produce R-squared for R=2^(64*w). -/
theorem r2_from_one (s : State) {base : BitVec 32} {len w : Nat}
    (h : DoubleLoopReady base len w (128 * w) s) (countFits : 128 * w < 2 ^ 32)
    (one : numAt s.mem (State.addr base) w 4 = 1) :
    WP isa doubleLoop s fun t => DoubleLoopReady base len w 0 t ∧
      numAt t.mem (State.addr base) w 4 = 2 ^ (128 * w) % numAt s.mem (State.addr base) w 0 ∧
      numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have hw : 2 ≤ w := h.width ▸ h.layout.1
  refine WP.mono (doubleLoop_ok s h (by omega) countFits) ?_
  rintro t ⟨ready, value, modulus, frame, rest⟩
  rw [one, Nat.mul_one] at value
  exact ⟨ready, value, modulus, frame, rest⟩

end VG.Proof.Bignum.Arm
