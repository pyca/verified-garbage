module
-- separate module: the proof of Appendix C.2's body is split in a chain of modules, so that a change rebuilds only the modules after it
public import VerifiedGarbage.Proof.Rsa.Arm.RdSqrtD

import VerifiedGarbage.Proof.Rsa.RecoverDet
import VerifiedGarbage.Proof.Rsa.Arm.KdDiv
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Ops
import VerifiedGarbage.Proof.Rsa.Arm.RdTaint
import VerifiedGarbage.Proof.Rsa.Arm.KeyWs
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Slots
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Ops2
import Mathlib.Tactic.Ring

/-! # `vg_rsa_recover_primes_det` on ARMv7: the square root's digit loop

The digit (`sqDigit_vp`) from its parts, and the math joining them: the estimate's conditions from
`sqrt_est`, the corrections from `fix_step`, and the next digit's root and remainder from `digit_rel`.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.RecoverDet
open VG VG.Arm VG.Proof.Mont VG.Proof.Rsa.Arm.Keys VG.Proof.Rsa.Arm.Recover
open VG.Impl.Rsa.Arm.Keys hiding aT1 aT2 aT3 aT4
open VG.Impl.Rsa.Arm.RecoverDet
open VG.Impl.Rsa.Arm.Recover (nArr)
open VG.Proof.X25519.Arm
open VG.Proof.Rsa (sub32 b2n)

/-! ## The digits' math -/

section
open VG.Spec.Rsa (isqrt)
open VG.Proof.Bignum.SqrtRem (IsDigit)

/-- `quot`'s 2-by-1 estimate, as a minimum. -/
theorem quot_min {U d : Nat} (hd : 0 < d) (h : U / 2 ^ 64 ≤ d) :
    (if U / 2 ^ 64 = d then 2 ^ 32 - 1 else U / 2 ^ 32 / d) = min (U / 2 ^ 32 / d) (2 ^ 32 - 1) := by
  have e : U / 2 ^ 32 / 2 ^ 32 = U / 2 ^ 64 := by rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
  split
  · rename_i h0
    have : 2 ^ 32 ≤ U / 2 ^ 32 / d := by
      rw [Nat.le_div_iff_mul_le hd]
      have := Nat.div_mul_le_self (U / 2 ^ 32) (2 ^ 32)
      rw [e, h0] at this; rw [Nat.mul_comm]; exact this
    omega
  · rename_i h0
    have : U / 2 ^ 32 / d < 2 ^ 32 := by
      rw [Nat.div_lt_iff_lt_mul hd]
      have : U / 2 ^ 32 / 2 ^ 32 < d := by omega
      rw [Nat.div_lt_iff_lt_mul (by decide)] at this; rw [Nat.mul_comm]; exact this
    omega

/-- The top word of the roots does not change. -/
theorem sJ_top {W x : Nat} : ∀ j, 1 ≤ j → 2 * j ≤ W → sJ W x j / 2 ^ (32 * (j - 1)) = sJ W x 1
  | 0, h, _ => absurd h (by decide)
  | 1, _, _ => by simp
  | j + 2, _, hW => by
    obtain ⟨g1, g2, -, -⟩ := digit_rel (W := W) (x := x) (j := j + 1) (by omega)
    rw [show sJ W x (j + 1 + 1) = sJ W x (j + 1) * 2 ^ 32 + (sJ W x (j + 1 + 1) - sJ W x (j + 1) * 2 ^ 32) by omega,
      show j + 2 - 1 = j + 1 from rfl, top_word g2 (by omega)]
    exact sJ_top (j + 1) (by omega) (by omega)

/-- The bounds a digit's operations need, for `s < 2^(32 j)`, `r ≤ 2 s`, `P < β²` and `y ≤ β + 1`. -/
theorem dig_bounds {j s r P y : Nat} (hs : s < 2 ^ (32 * j)) (hr : r ≤ 2 * s) (hP : P < 2 ^ 64)
    (hy : y ≤ 2 ^ 32 + 1) :
    2 * (r * 2 ^ 64 + P + 1) ≤ 2 ^ (32 * (j + 3)) ∧ 2 * ((2 * s * 2 ^ 32 + y) * y) < 2 ^ (32 * (j + 3)) ∧
      2 * s * 2 ^ 32 + 2 * y < 2 ^ (32 * (j + 3)) ∧ r * 2 ^ 64 + P < 2 ^ (32 * (j + 3)) ∧
      y * (2 * s * 2 ^ 32) < 2 ^ (32 * (j + 3)) ∧ r < 2 ^ (32 * j + 1) := by
  have eM : (2 : Nat) ^ (32 * (j + 3)) = 2 ^ (32 * j) * 2 ^ 96 := by rw [← Nat.pow_add]; congr 1
  have e1 : (2 : Nat) ^ (32 * j + 1) = 2 ^ (32 * j) * 2 := Nat.pow_succ ..
  rw [eM, e1]
  clear eM e1
  generalize 2 ^ (32 * j) = T at hs ⊢
  simp only [show (2 : Nat) ^ 32 = 4294967296 from rfl, show (2 : Nat) ^ 64 = 18446744073709551616 from rfl,
    show (2 : Nat) ^ 96 = 79228162514264337593543950336 from rfl] at hP hy ⊢
  have c0 : 2 * s * 4294967296 ≤ 2 * T * 4294967296 :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hs.le)
  have m1 : (2 * s * 4294967296 + y) * y ≤ (2 * T * 4294967296 + 4294967297) * 4294967297 :=
    Nat.mul_le_mul (by omega_using [hs, hy]) hy
  have m2 : y * (2 * s * 4294967296) ≤ 4294967297 * (2 * T * 4294967296) := Nat.mul_le_mul hy c0
  have m3 : r * 18446744073709551616 ≤ 2 * T * 18446744073709551616 :=
    Nat.mul_le_mul_right _ (by omega_using [hs, hr])
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · omega_using [hs, hP, m3]
  · omega_using [hs, m1]
  · omega_using [hs, hy, c0]
  · omega_using [hs, hP, m3]
  · omega_using [hs, m2]
  · omega_using [hs, hr]

end

/-! ## A digit -/

section
variable {P : RP}
open VG.Impl.Rsa.Arm.KeyDiv (sD sD1 sV sQ sMk sU0 sU2)
open VG.Proof.Bignum.SqrtRem (IsDigit)
open VG.Proof.Bignum.WordStep32 (twos_eq)

/-- `X'` with its top `2 j` words replaced by the remainder of their root. -/
abbrev Rv (W x j : Nat) : Nat := x % 2 ^ (32 * (W - 2 * j)) + 2 ^ (32 * (W - 2 * j)) * rJ W x j

/-- `D = 2 s` for the root `s` of `X'`'s top `2 j` words, top-aligned: from word `W / 2 - j`. -/
abbrev Dv (W x j : Nat) : Nat := 2 ^ (32 * (W / 2 - j)) * (2 * sJ W x j)

/-- The wide arrays before digit `j`: `[wR]` the remainder in place, `[wD]` `D` and `[wE]` its complement. -/
abbrev DAW (W j : Nat) (aw : Nat → Nat) : Nat → Nat :=
  upd (upd (upd aw wR (Rv W (aw wR) j)) wD (Dv W (aw wR) j)) wE (cmpl W (Dv W (aw wR) j))

/-- The slots before digit `j` of `K + 1`: `d₁` (the second word of `s β`), the offsets, the length, `D`'s
offset and the count. -/
abbrev DV (W K j sw : Nat) (v : Nat → Nat) : Nat → Nat :=
  upd (upd (upd (upd (upd (upd v sD1 (sw * 2 ^ 32 / 2 ^ (32 * (j - 1)) % 2 ^ 32))
    sPo ((4 * W + 2 ^ 32 - 8 * j - 8) % 2 ^ 32)) sMo (4 * j)) sLn (j + 3))
    sCm ((2 * W + 2 ^ 32 - 4 - 4 * j) % 2 ^ 32)) sK (K + 1 - j)

/-- A digit's values: the remainder `R = r β² + P`, `c = 2 s β`, the digit and its estimate. -/
abbrev dR (W x j : Nat) : Nat := rJ W x j * 2 ^ 64 + pairP W x j
abbrev dC (W x j : Nat) : Nat := 2 * sJ W x j * 2 ^ 32
abbrev dQ (W x j : Nat) : Nat := sJ W x (j + 1) - sJ W x j * 2 ^ 32
abbrev dQh (W x j : Nat) : Nat :=
  min (dR W x j / 2 ^ (32 * (j - 1) + 1) / (sJ W x j * 2 ^ 32 / 2 ^ (32 * (j - 1)))) (2 ^ 32 - 1)
/-- After the first correction. -/
abbrev dX (W x j : Nat) : Nat := dQh W x j - if dQ W x j < dQh W x j then 1 else 0

/-- The math of digit `j`. -/
theorem dig_math {W x j : Nat} (hx1 : 2 ^ (32 * W - 2) ≤ x) (hx2 : x < 2 ^ (32 * W)) (hj : 1 ≤ j)
    (hjW : 2 * j + 2 ≤ W) :
    (2 ^ (32 * j - 1) ≤ sJ W x j ∧ sJ W x j < 2 ^ (32 * j)) ∧ rJ W x j ≤ 2 * sJ W x j ∧
    sJ W x j * 2 ^ 32 + dQ W x j = sJ W x (j + 1) ∧ dQ W x j < 2 ^ 32 ∧
    IsDigit (2 ^ 32) (sJ W x j) (dR W x j) (dQ W x j) ∧
    rJ W x (j + 1) = dR W x j - (dC W x j + dQ W x j) * dQ W x j ∧
    dR W x j / (2 * 2 ^ (32 * (j - 1))) / 2 ^ 64 ≤ sJ W x j * 2 ^ 32 / 2 ^ (32 * (j - 1)) / 2 ^ 32 ∧
    dR W x j / (2 * 2 ^ (32 * (j - 1))) < (2 ^ 32 + 1) * (sJ W x j * 2 ^ 32 / 2 ^ (32 * (j - 1))) ∧
    dQh W x j ≤ min (dR W x j / (2 * 2 ^ (32 * (j - 1))) / 2 ^ 32 /
      (sJ W x j * 2 ^ 32 / 2 ^ (32 * (j - 1)) / 2 ^ 32)) (2 ^ 32 - 1) ∧
    min (dR W x j / (2 * 2 ^ (32 * (j - 1))) / 2 ^ 32 / (sJ W x j * 2 ^ 32 / 2 ^ (32 * (j - 1)) / 2 ^ 32))
      (2 ^ 32 - 1) ≤ dQh W x j + 2 ∧
    dQ W x j ≤ dQh W x j ∧ dQh W x j ≤ dQ W x j + 2 ∧
    sJ W x j * 2 ^ 32 / 2 ^ (32 * (j - 1)) / 2 ^ 32 = sJ W x 1 := by
  have sb := sJ_bounds hx1 hx2 hj (by omega)
  obtain ⟨-, rl⟩ := rJ_le (W := W) (x := x) (j := j)
  obtain ⟨g1, g2, dg, rr⟩ := digit_rel (W := W) (x := x) hjW
  have Pl : pairP W x j < 2 ^ 64 := Nat.mod_lt _ (by decide)
  have hs : 2 ^ 32 * 2 ^ (32 * (j - 1)) ≤ 2 * sJ W x j := by
    rw [← Nat.pow_add, show 32 + 32 * (j - 1) = (32 * j - 1) + 1 by omega, Nat.pow_succ]; omega
  have hR : dR W x j < (2 * sJ W x j + 1) * 2 ^ 64 := by
    have := Nat.mul_le_mul_right (2 ^ 64) rl
    simp only [dR]; rw [Nat.add_mul, Nat.one_mul]; omega
  have est := sqrt_est (K := 32 * (j - 1)) (by omega) hs hR dg g2
  have eP : dR W x j / 2 ^ (32 * (j - 1) + 1) = dR W x j / (2 * 2 ^ (32 * (j - 1))) := by
    rw [Nat.pow_succ, Nat.mul_comm]
  have e1 : sJ W x j * 2 ^ 32 / 2 ^ (32 * (j - 1)) / 2 ^ 32 = sJ W x 1 := by
    rw [Nat.div_div_eq_div_mul, Nat.mul_comm (2 ^ (32 * (j - 1))), ← Nat.div_div_eq_div_mul,
      Nat.mul_div_cancel _ (by decide)]
    exact sJ_top j hj (by omega)
  simp only [dQh, eP]
  exact ⟨sb, rl, by simp only [dQ]; omega, g2, dg, rr, est.1, est.2.1, est.2.2.1, est.2.2.2.1, est.2.2.2.2.1,
    est.2.2.2.2.2, e1⟩

end

section
variable {P : RP}
open VG.Impl.Rsa.Arm.KeyDiv (sD sD1 sV sQ sMk sU0 sU2)

theorem twos_lt (n : Nat) (v : Int) : VG.Proof.Bignum.WordStep32.twos (2 ^ (32 * n)) v < 2 ^ (32 * n) := by
  unfold VG.Proof.Bignum.WordStep32.twos
  have := Int.emod_lt_of_pos v (show (0 : Int) < ((2 ^ (32 * n) : Nat) : Int) by exact_mod_cast Nat.two_pow_pos _)
  have := Int.emod_nonneg v (show ((2 ^ (32 * n) : Nat) : Int) ≠ 0 by exact_mod_cast (Nat.two_pow_pos _).ne')
  omega

theorem twos_nat (n a : Nat) (ha : a < 2 ^ (32 * n)) :
    VG.Proof.Bignum.WordStep32.twos (2 ^ (32 * n)) (a : Int) = a := by
  unfold VG.Proof.Bignum.WordStep32.twos
  rw [Int.emod_eq_of_lt (by omega) (by exact_mod_cast ha)]; simp

theorem mul_two32_div {y j : Nat} (hj : 1 ≤ j) : y * 2 ^ 32 / 2 ^ (32 * j) = y / 2 ^ (32 * (j - 1)) := by
  rw [show 32 * j = 32 * (j - 1) + 32 by omega, Nat.pow_add, Nat.mul_div_mul_right _ _ (by decide)]

end

/-! ## A digit's arrays -/

section
open VG.Proof.Bignum.WordStep32 (twos)

/-- `X'` below word `b`, and `T` from it. -/
abbrev Rs (x b T : Nat) : Nat := x % 2 ^ (32 * b) + 2 ^ (32 * b) * T

theorem Rs_div {x b T : Nat} : Rs x b T % 2 ^ (32 * b) = x % 2 ^ (32 * b) ∧ Rs x b T / 2 ^ (32 * b) = T :=
  mod_div_of (Nat.two_pow_pos _) (Nat.mod_lt _ (Nat.two_pow_pos _)) rfl

theorem Rs_win {x b k T v : Nat} (hT : T < 2 ^ (32 * k)) : setWin (Rs x b T) b k v = Rs x b v := by
  have h2 : Rs x b T / 2 ^ (32 * (b + k)) = 0 := by
    rw [pow32_add, ← Nat.div_div_eq_div_mul, Rs_div.2, Nat.div_eq_of_lt hT]
  show Rs x b T % 2 ^ (32 * b) + 2 ^ (32 * b) * (v + 2 ^ (32 * k) * (Rs x b T / 2 ^ (32 * (b + k)))) = _
  rw [Rs_div.1, h2, Nat.mul_zero, Nat.add_zero]

theorem Rs_top {x b n T : Nat} : Rs x b T / 2 ^ (32 * (b + n)) % 2 ^ 32 = T / 2 ^ (32 * n) % 2 ^ 32 := by
  rw [pow32_add, ← Nat.div_div_eq_div_mul, Rs_div.2]

/-- The window's low words and then its top word. -/
theorem Rs_row {x b n T L t : Nat} (hT : T < 2 ^ (32 * (n + 1))) (hL : L < 2 ^ (32 * n)) :
    setW (setWin (Rs x b T) b n L) (b + n) t = Rs x b (L + 2 ^ (32 * n) * t) := by
  rw [setW_eq_win, setWin_adj hL, Rs_win hT]

/-- The remainder in place: `X'`'s words below `b = W - 2 j - 2` and `R = r β² + P` from `b`. -/
theorem Rv_Rs {W x j : Nat} (hjW : 2 * j + 2 ≤ W) : Rv W x j = Rs x (W - 2 * j - 2) (dR W x j) := by
  have e : (2 : Nat) ^ (32 * (W - 2 * j)) = 2 ^ (32 * (W - 2 * j - 2)) * 2 ^ 64 := by
    rw [← Nat.pow_add]; congr 1; omega
  simp only [Rv, Rs, dR, pairP]
  rw [e, Nat.mod_mul]
  ring

theorem Rv_succ {W x j : Nat} (hjW : 2 * j + 2 ≤ W) : Rv W x (j + 1) = Rs x (W - 2 * j - 2) (rJ W x (j + 1)) := by
  simp only [Rv, Rs]; rw [show W - 2 * (j + 1) = W - 2 * j - 2 by omega]

theorem top_val {N a t : Nat} (hN : 0 < N) :
    a % N + N * ((t + a / N) % 2 ^ 32) = (a + N * t) % (N * 2 ^ 32) := by
  rw [Nat.mod_mul, Nat.add_mul_mod_self_left, Nat.add_mul_div_left _ _ hN, Nat.add_comm (a / N)]

/-- The row of the multiply-subtract and its top word: `R - (c + q) q` modulo `2^(32 (n + 1))`. -/
theorem ms_val {n R c q : Nat} (hq : q < 2 ^ 32) (hc : c + q < 2 ^ (32 * n)) (hR : R < 2 ^ (32 * (n + 1))) :
    (R % 2 ^ (32 * n) + q * (2 ^ (32 * n) - 1 - (c + q)) + q) % 2 ^ (32 * n) + 2 ^ (32 * n) *
      ((2 ^ 32 - q + (R / 2 ^ (32 * n) % 2 ^ 32 +
        (R % 2 ^ (32 * n) + q * (2 ^ (32 * n) - 1 - (c + q)) + q) / 2 ^ (32 * n)) % 2 ^ 32) % 2 ^ 32) =
    twos (2 ^ (32 * (n + 1))) ((R : Int) - ((c + q) * q : Nat)) := by
  have hN := Nat.two_pow_pos (32 * n)
  have eM : (2 : Nat) ^ (32 * (n + 1)) = 2 ^ (32 * n) * 2 ^ 32 := by rw [pow32_add, Nat.mul_one]
  generalize ea : R % 2 ^ (32 * n) + q * (2 ^ (32 * n) - 1 - (c + q)) + q = a
  rw [Nat.add_mod_mod, ← Nat.add_assoc (2 ^ 32 - q), top_val hN, ← eM]
  refine eq_twos (Nat.mod_lt _ (Nat.two_pow_pos _)) ?_
  have hd : R / 2 ^ (32 * n) < 2 ^ 32 := by rw [Nat.div_lt_iff_lt_mul hN, Nat.mul_comm, ← eM]; exact hR
  rw [Nat.mod_eq_of_lt hd]
  have hr := Nat.div_add_mod R (2 ^ (32 * n))
  have key : ((a + 2 ^ (32 * n) * (2 ^ 32 - q + R / 2 ^ (32 * n)) : Nat) : Int) =
      (R : Int) - ((c + q) * q : Nat) + ((2 ^ (32 * (n + 1)) : Nat) : Int) := by
    rw [← ea, eM]
    have h1 : c + q ≤ 2 ^ (32 * n) - 1 := by omega
    have hq' : q ≤ 4294967296 := by omega
    generalize R / 2 ^ (32 * n) = u at hr ⊢
    generalize R % 2 ^ (32 * n) = v at hr ⊢
    subst hr
    push_cast [Nat.cast_sub h1, Nat.cast_sub hq', Nat.cast_sub (show 1 ≤ 2 ^ (32 * n) by omega)]
    ring
  rw [Int.natCast_emod, Int.emod_emod_of_dvd _ (dvd_refl _), key, Int.add_emod_right]

/-- A correction's row and its top word: `T + y` modulo `2^(32 (n + 1))`. -/
theorem corr_val {n T y : Nat} (hT : T < 2 ^ (32 * (n + 1))) :
    (T % 2 ^ (32 * n) + y) % 2 ^ (32 * n) + 2 ^ (32 * n) * ((T / 2 ^ (32 * n) % 2 ^ 32 +
      (T % 2 ^ (32 * n) + y) / 2 ^ (32 * n)) % 2 ^ 32) = (T + y) % 2 ^ (32 * (n + 1)) := by
  have hN := Nat.two_pow_pos (32 * n)
  have eM : (2 : Nat) ^ (32 * (n + 1)) = 2 ^ (32 * n) * 2 ^ 32 := by rw [pow32_add, Nat.mul_one]
  have hd : T / 2 ^ (32 * n) < 2 ^ 32 := by rw [Nat.div_lt_iff_lt_mul hN, Nat.mul_comm, ← eM]; exact hT
  have e : T % 2 ^ (32 * n) + y + 2 ^ (32 * n) * (T / 2 ^ (32 * n)) = T + y := by
    have := Nat.div_add_mod T (2 ^ (32 * n)); omega
  rw [Nat.mod_eq_of_lt hd, top_val hN, ← eM, e]

/-- The sign of `T`: its top word's top bit. -/
theorem sign_val {n T : Nat} (hT : T < 2 ^ (32 * (n + 1))) :
    T / 2 ^ (32 * n) % 2 ^ 32 / 2 ^ 31 = T / 2 ^ (32 * (n + 1) - 1) := by
  have hN := Nat.two_pow_pos (32 * n)
  have eM : (2 : Nat) ^ (32 * (n + 1)) = 2 ^ (32 * n) * 2 ^ 32 := by rw [pow32_add, Nat.mul_one]
  have hd : T / 2 ^ (32 * n) < 2 ^ 32 := by rw [Nat.div_lt_iff_lt_mul hN, Nat.mul_comm, ← eM]; exact hT
  rw [Nat.mod_eq_of_lt hd, Nat.div_div_eq_div_mul, ← Nat.pow_add]; congr 2

/-- A correction by its sign. -/
theorem fixR_eq {n t c x : Nat} (hn : 2 ≤ n) (ht : t < 2 ^ (32 * n)) (hx : t / 2 ^ (32 * n - 1) ≠ 0 → 1 ≤ x)
    (hc : c + 2 * x < 2 ^ (32 * n)) (hx64 : 2 * x < 2 ^ 64) :
    fixR n t c x = (t + t / 2 ^ (32 * n - 1) * (c + 2 * x - 1)) % 2 ^ (32 * n) := by
  unfold fixR fixG
  split
  · rename_i h0
    rw [h0, Nat.zero_mul, Nat.add_zero, show sub32 n t (sub32 n 0 0) = t by unfold sub32; simp [Nat.mod_eq_of_lt ht]]
    exact (Nat.mod_eq_of_lt ht).symm
  · rename_i h0
    have x1 := hx h0
    have h64 : (2 : Nat) ^ 64 ≤ 2 ^ (32 * n) := Nat.pow_le_pow_right (by decide) (by omega)
    have t1 : t / 2 ^ (32 * n - 1) = 1 := by
      have : t / 2 ^ (32 * n - 1) < 2 := by
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_succ']
        exact Nat.lt_of_lt_of_le ht (Nat.pow_le_pow_right (by decide) (by omega))
      generalize t / 2 ^ (32 * n - 1) = g at this h0 ⊢
      omega
    have eE : fixE x = 2 * x - 1 := by
      unfold fixE; rw [show 2 * x + 2 ^ 64 - 1 = (2 * x - 1) + 2 ^ 64 by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    have eG : sub32 n c (sub32 n 0 (2 * x - 1)) = c + 2 * x - 1 := by
      rw [sub32_negadd (by omega) (by omega), Nat.mod_eq_of_lt (by omega)]; omega
    rw [eE, eG, sub32_negadd ht (by omega), t1, Nat.one_mul]

/-- A correction's row, `x (D' + q - 1)` for the sign `x`. -/
theorem corr_row {t c q x : Nat} (hx : x ≤ 1) (hq : x = 1 → 1 ≤ q) (hq32 : q < 2 ^ 32) :
    t + x * (c + q) + x * ((q + 2 ^ 32 - 1) % 2 ^ 32) = t + x * (c + 2 * q - 1) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hx with rfl | rfl
  · rw [Nat.zero_mul, Nat.zero_mul, Nat.zero_mul]
  · have q1 := hq rfl
    have e : (q + 2 ^ 32 - 1) % 2 ^ 32 = q - 1 := by
      rw [show q + 2 ^ 32 - 1 = (q - 1) + 2 ^ 32 by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [e, Nat.one_mul, Nat.one_mul, Nat.one_mul]; omega

/-- `D`'s words from `m`: `y β + q`. -/
abbrev Dq (m y q : Nat) : Nat := 2 ^ (32 * m) * (y * 2 ^ 32 + q)

theorem Dq_div {m y q : Nat} (hq : q < 2 ^ 32) :
    Dq m y q % 2 ^ (32 * m) = 0 ∧ Dq m y q / 2 ^ (32 * (m + 1)) = y := by
  have e := mod_div_of (x := Dq m y q) (l := 0) (q := y * 2 ^ 32 + q) (Nat.two_pow_pos (32 * m))
    (Nat.two_pow_pos _) (by simp)
  refine ⟨e.1, ?_⟩
  rw [pow32_add, Nat.mul_one, ← Nat.div_div_eq_div_mul, e.2, Nat.add_comm, Nat.add_mul_div_right _ _ (by decide),
    Nat.div_eq_of_lt hq, Nat.zero_add]

theorem Dq_set {m y q a : Nat} (hq : q < 2 ^ 32) : setW (Dq m y q) m a = Dq m y a := by
  show Dq m y q % 2 ^ (32 * m) + 2 ^ (32 * m) * (a + 2 ^ 32 * (Dq m y q / 2 ^ (32 * (m + 1)))) = _
  rw [(Dq_div hq).1, (Dq_div hq).2, Nat.zero_add, Nat.add_comm a, Nat.mul_comm (2 ^ 32)]

theorem Dq_win {m y q n : Nat} (h : y * 2 ^ 32 + q < 2 ^ (32 * n)) :
    Dq m y q / 2 ^ (32 * m) % 2 ^ (32 * n) = y * 2 ^ 32 + q := by
  rw [Nat.mul_div_cancel_left _ (Nat.two_pow_pos _), Nat.mod_eq_of_lt h]

theorem Dq_lt {W m k y q : Nat} (hk0 : 0 < k) (hk : m + k + 1 ≤ W) (hy : y < 2 ^ (32 * k)) (hy2 : y % 2 = 0)
    (hq : q < 2 ^ 33) : y * 2 ^ 32 + q < 2 ^ (32 * (k + 1)) ∧ Dq m y q < 2 ^ (32 * W) := by
  have e1 : (2 : Nat) ^ (32 * (k + 1)) = 2 ^ (32 * k) * 2 ^ 32 := by rw [pow32_add, Nat.mul_one]
  have ev : 2 ^ (32 * k) % 2 = 0 := by
    rw [show 32 * k = (32 * k - 1) + 1 by omega, Nat.pow_succ]; simp
  have l1 : y * 2 ^ 32 + q < 2 ^ (32 * (k + 1)) := by
    rw [e1]
    have : y + 2 ≤ 2 ^ (32 * k) := by omega
    have := Nat.mul_le_mul_right (2 ^ 32) this
    simp only [show (2 : Nat) ^ 32 = 4294967296 from rfl, show (2 : Nat) ^ 33 = 8589934592 from rfl] at *
    omega
  refine ⟨l1, ?_⟩
  calc Dq m y q < 2 ^ (32 * m) * 2 ^ (32 * (k + 1)) := Nat.mul_lt_mul_of_pos_left l1 (Nat.two_pow_pos _)
    _ = 2 ^ (32 * (m + (k + 1))) := (pow32_add _ _).symm
    _ ≤ 2 ^ (32 * W) := Nat.pow_le_pow_right (by decide) (by omega)

theorem C_win {W m n y q : Nat} (hmn : m + n ≤ W) (hx : Dq m y q < 2 ^ (32 * W))
    (h : y * 2 ^ 32 + q < 2 ^ (32 * n)) :
    cmpl W (Dq m y q) / 2 ^ (32 * m) % 2 ^ (32 * n) = 2 ^ (32 * n) - 1 - (y * 2 ^ 32 + q) := by
  rw [win_cmpl hmn hx, Dq_win h]

theorem C_set {W m y q a : Nat} (hm : m < W) (hx : Dq m y q < 2 ^ (32 * W)) (hq : q < 2 ^ 32) (ha : a < 2 ^ 32) :
    setW (cmpl W (Dq m y q)) m (2 ^ 32 - 1 - a) = cmpl W (Dq m y a) := by
  rw [← cmpl_setW hm hx ha, Dq_set hq]

theorem Dq_finish' {m y q : Nat} (hq : q < 2 ^ 32) (hy : y % 2 = 0) :
    setW (Dq m y (2 * q % 2 ^ 32)) (m + 1) ((y % 2 ^ 32 + q / 2 ^ 31) % 2 ^ 32) =
      2 ^ (32 * m) * (y * 2 ^ 32 + 2 * q) := by
  have a1 : 2 * q % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
  have e1 : (y % 2 ^ 32 + q / 2 ^ 31) % 2 ^ 32 = y % 2 ^ 32 + q / 2 ^ 31 := Nat.mod_eq_of_lt (by omega)
  rw [e1]
  show Dq m y (2 * q % 2 ^ 32) % 2 ^ (32 * (m + 1)) + 2 ^ (32 * (m + 1)) * (y % 2 ^ 32 + q / 2 ^ 31 +
    2 ^ 32 * (Dq m y (2 * q % 2 ^ 32) / 2 ^ (32 * (m + 1 + 1)))) = _
  have d1 := (Dq_div (m := m) (y := y) a1).2
  have e2 : Dq m y (2 * q % 2 ^ 32) / 2 ^ (32 * (m + 1 + 1)) = y / 2 ^ 32 := by
    rw [show 32 * (m + 1 + 1) = 32 * (m + 1) + 32 by omega, Nat.pow_add, ← Nat.div_div_eq_div_mul, d1]
  have e3 : Dq m y (2 * q % 2 ^ 32) % 2 ^ (32 * (m + 1)) = 2 ^ (32 * m) * (2 * q % 2 ^ 32) := by
    rw [pow32_add, Nat.mul_one, Nat.mul_mod_mul_left]
    congr 1
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt a1]
  rw [e2, e3, pow32_add, Nat.mul_one, Nat.mul_assoc, ← Nat.mul_add]
  congr 1
  omega

/-- `D := 2 s'`: `2 q`'s low word at `m`, and `y` plus its top bit at `m + 1`. -/
theorem Dq_finish {m y q : Nat} (hq : q < 2 ^ 32) (hy : y % 2 = 0) :
    setW (setW (Dq m y q) m (2 * q % 2 ^ 32)) (m + 1)
      ((Dq m y q / 2 ^ (32 * (m + 1)) % 2 ^ 32 + q / 2 ^ 31) % 2 ^ 32) = 2 ^ (32 * m) * (y * 2 ^ 32 + 2 * q) := by
  rw [Dq_set hq, (Dq_div hq).2, Dq_finish' hq hy]

/-- And `C` its complement. -/
theorem C_finish {W m k y q q0 : Nat} (hk0 : 0 < k) (hk : m + k + 1 ≤ W) (hy : y < 2 ^ (32 * k))
    (hy2 : y % 2 = 0) (hq : q < 2 ^ 32) (hq0 : q0 < 2 ^ 32) (hm2 : m + 2 ≤ W) :
    setW (setW (cmpl W (Dq m y q0)) m (2 ^ 32 - 1 - 2 * q % 2 ^ 32)) (m + 1)
      ((2 ^ 32 - q / 2 ^ 31 + cmpl W (Dq m y q0) / 2 ^ (32 * (m + 1)) % 2 ^ 32) % 2 ^ 32) =
    cmpl W (2 ^ (32 * m) * (y * 2 ^ 32 + 2 * q)) := by
  have a1 : 2 * q % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
  have l0 := (Dq_lt (q := q0) hk0 hk hy hy2 (by omega)).2
  have la := (Dq_lt (q := 2 * q % 2 ^ 32) hk0 hk hy hy2 (by omega)).2
  have w1 : cmpl W (Dq m y q0) / 2 ^ (32 * (m + 1)) % 2 ^ 32 = 2 ^ 32 - 1 - y % 2 ^ 32 := by
    have := win_cmpl (W := W) (o := m + 1) (n := 1) (by omega) l0
    rw [Nat.mul_one] at this
    rw [this, (Dq_div hq0).2]
  rw [w1, C_set (by omega) l0 hq0 a1, ← Dq_finish' hq hy2,
    cmpl_setW (by omega) la (Nat.mod_lt _ (by decide))]
  congr 1
  omega

/-- `d₁`: the word `k` of `s` from the words `k` and `k + 1` of `2 s`. -/
theorem d1_val {s k : Nat} :
    (2 * s / 2 ^ (32 * k)) % 2 ^ 32 / 2 + (2 * s / 2 ^ (32 * (k + 1))) % 2 ^ 32 % 2 * 2 ^ 31 =
      s / 2 ^ (32 * k) % 2 ^ 32 := by
  have e1 : 2 * s / 2 ^ (32 * k) / 2 = s / 2 ^ (32 * k) := by
    rw [Nat.div_div_eq_div_mul, Nat.mul_comm (2 ^ (32 * k)) 2, Nat.mul_div_mul_left _ _ (by decide)]
  have e2 : 2 * s / 2 ^ (32 * (k + 1)) = 2 * s / 2 ^ (32 * k) / 2 ^ 32 := by
    rw [pow32_add, Nat.mul_one, Nat.div_div_eq_div_mul]
  rw [e2, ← e1]
  generalize 2 * s / 2 ^ (32 * k) = u
  omega

theorem mul_pow_div {m k z : Nat} : 2 ^ (32 * m) * z / 2 ^ (32 * (m + k)) = z / 2 ^ (32 * k) := by
  rw [pow32_add, ← Nat.div_div_eq_div_mul, Nat.mul_div_cancel_left _ (Nat.two_pow_pos _)]

theorem Dv_Dq {W x j : Nat} (hj : j + 1 ≤ W / 2) : Dv W x j = Dq (W / 2 - 1 - j) (2 * sJ W x j) 0 := by
  simp only [Dv, Dq, Nat.add_zero]
  rw [show W / 2 - j = W / 2 - 1 - j + 1 by omega, pow32_add, Nat.mul_one, Nat.mul_assoc, Nat.mul_comm (2 ^ 32)]

theorem upd3_1 {a : Nat → Nat} {i k l u v w u' : Nat} (hik : i ≠ k) (hil : i ≠ l) :
    Keys.upd (Keys.upd (Keys.upd (Keys.upd a i u) k v) l w) i u' =
      Keys.upd (Keys.upd (Keys.upd a i u') k v) l w := by
  funext z; simp only [Keys.upd]; split_ifs <;> omega

theorem upd3_2 {a : Nat → Nat} {i k l u v w v' : Nat} (hkl : k ≠ l) :
    Keys.upd (Keys.upd (Keys.upd (Keys.upd a i u) k v) l w) k v' =
      Keys.upd (Keys.upd (Keys.upd a i u) k v') l w := by
  funext z; simp only [Keys.upd]; split_ifs <;> omega

theorem upd3_3 {a : Nat → Nat} {i k l u v w w' : Nat} :
    Keys.upd (Keys.upd (Keys.upd (Keys.upd a i u) k v) l w) l w' =
      Keys.upd (Keys.upd (Keys.upd a i u) k v) l w' := by
  funext z; simp only [Keys.upd]; split_ifs <;> omega

theorem upd_upd {a : Nat → Nat} {i u v : Nat} : Keys.upd (Keys.upd a i u) i v = Keys.upd a i v := by
  funext z; simp only [Keys.upd]; split_ifs <;> omega

end

/-- A stage's arrays and slots, as other functions give them where `E` holds. -/
theorem Dk_congr {P : RP} {E : State → Prop} {A AW AW' V V' : State → Nat → Nat} {L LW LS : List Nat} {v N : Nat}
    {σ s : State} (h : Dk P E A L AW LW V LS v N σ s) (ha : E σ → AW σ = AW' σ) (hv : E σ → V σ = V' σ) :
    Dk P E A L AW' LW V' LS v N σ s := by
  obtain ⟨e, k, w⟩ := h; rw [ha e, hv e] at k; exact ⟨e, k, w⟩

/-- The arrays within digit `j`: `[wR]` `R`'s place holding `T`, `[wD]` `D'` with `q_d` and `[wE]` the
complement of `D'` with `q_e`. -/
abbrev dA (W j : Nat) (aw : Nat → Nat) (T qd qe : Nat) : Nat → Nat :=
  upd (upd (upd aw wR (Rs (aw wR) (W - 2 * j - 2) T)) wD (Dq (W / 2 - 1 - j) (2 * sJ W (aw wR) j) qd)) wE
    (cmpl W (Dq (W / 2 - 1 - j) (2 * sJ W (aw wR) j) qe))


/-- A stage within digit `j`: the arrays `dA` and `q̂` at `sQ`. -/
abbrev dStage (P : RP) (E : State → Prop) (A : State → Nat → Nat) (L : List Nat) (AW V : State → Nat → Nat)
    (LW LS : List Nat) (K j : Nat) (T qd qe q : State → Nat) : State → State → Prop :=
  Dk P E A L (fun σ => dA P.W j (AW σ) (T σ) (qd σ) (qe σ)) LW
    (fun σ => upd (DV P.W K j (sJ P.W (AW σ wR) j) (V σ)) VG.Impl.Rsa.Arm.KeyDiv.sQ (q σ))
    (VG.Impl.Rsa.Arm.KeyDiv.sQ :: LS) P.W 22

/-- A piece's post-stage, with its arrays and slots as other functions give them. -/
theorem dk_post {P : RP} {E : State → Prop} {A AW AW' V V' : State → Nat → Nat} {L LW LS : List Nat} {v N : Nat}
    {F : State → State → Prop} {c : Prog isa} (h : VP F c (Dk P E A L AW LW V LS v N))
    (ha : ∀ σ, E σ → AW σ = AW' σ) (hv : ∀ σ, E σ → V σ = V' σ) : VP F c (Dk P E A L AW' LW V' LS v N) :=
  h.mono (fun _ _ h => h) fun σ _ h => Dk_congr h (ha σ) (hv σ)

section
variable {P : RP}
open VG.Impl.Rsa.Arm.KeyDiv (sD sD1 sV sQ sMk sU0 sU2)
open VG.Proof.Bignum.WordStep32 (twos)

/-- The slots a digit's pointers read. -/
theorem dSlots {W K j : Nat} {sw q : Nat} {v : Nat → Nat} (hjW : 2 * j + 2 ≤ W) (hKW : 2 * K + 2 = W) (Wl : W ≤ 518) :
    upd (DV W K j sw v) sQ q sPo = 4 * (W - 2 * j - 2) ∧ upd (DV W K j sw v) sQ q sCm = 4 * (W / 2 - 1 - j) ∧
      upd (DV W K j sw v) sQ q sLn = j + 2 + 1 ∧ upd (DV W K j sw v) sQ q sQ = q := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rd_up <;> omega

/-- A correction: where `T < 0`, `T += D' + q̂ - 1` and `q̂ -= 1`. -/
theorem correct_vp {K j : Nat} (j1 : 1 ≤ j) (hjW : 2 * j + 2 ≤ P.W) (hKW : 2 * K + 2 = P.W)
    {L LW LS : List Nat} {E : State → Prop} {A AW V : State → Nat → Nat} {T q q0 : State → Nat}
    (hR : wR ∈ LW) (hD : wD ∈ LW) (hL : ∀ i ∈ L, i / 2 ≠ wR ∧ i / 2 ≠ wD)
    (hLn : sLn ∈ LS) (hPo : sPo ∈ LS) (hCm : sCm ∈ LS)
    (hy : ∀ σ, E σ → 2 * sJ P.W (AW σ wR) j < 2 ^ (32 * (j + 1)))
    (hT : ∀ σ, E σ → T σ < 2 ^ (32 * (j + 2 + 1)))
    (hg : ∀ σ, E σ → T σ / 2 ^ (32 * (j + 2 + 1) - 1) ≤ 1)
    (hq1 : ∀ σ, E σ → T σ / 2 ^ (32 * (j + 2 + 1) - 1) = 1 → 1 ≤ q σ) (hq : ∀ σ, E σ → q σ < 2 ^ 32)
    (hc : ∀ σ, E σ → dC P.W (AW σ wR) j + 2 * q σ < 2 ^ (32 * (j + 2 + 1))) :
    VP (dStage P E A L AW V LW LS K j T q q0 q) correct
      (dStage P E A L AW V LW LS K j (fun σ => fixR (j + 2 + 1) (T σ) (dC P.W (AW σ wR) j) (q σ))
        (fun σ => q σ - T σ / 2 ^ (32 * (j + 2 + 1) - 1)) q0 (fun σ => q σ - T σ / 2 ^ (32 * (j + 2 + 1) - 1))) := by
  refine VP.of_imp (p := P.W ≤ 518) (fun σ s h => h.2.1.sizes.Wle) fun Wl => ?_
  have mQ : ∀ {d}, d ∈ LS → d ∈ sQ :: LS := fun h => List.mem_cons_of_mem _ h
  have sl := fun (σ : State) => dSlots (sw := sJ P.W (AW σ wR) j) (q := q σ) (v := V σ) hjW hKW Wl
  have mk : P.W / 2 - 1 - j + (j + 1) + 1 ≤ P.W := by omega
  simp only [correct, seqs]
  refine VP.seq (dPtrs_vp (P := P) (d := wD) (b := P.W - 2 * j - 2) (m := P.W / 2 - 1 - j) (n := j + 2) (by decide)
    (mQ hPo) (mQ hCm) (mQ hLn) (fun σ _ => (sl σ).1) (fun σ _ => (sl σ).2.1) (fun σ _ => (sl σ).2.2.1)
    (by omega) ptrsD_taint) ?_
  refine VP.seq (corrRow_vp (P := P) (b := P.W - 2 * j - 2) (m := P.W / 2 - 1 - j) (n := j + 2) (by omega)
    (by omega) (by omega) hR hD (List.mem_cons_self ..) (mQ hCm) (fun σ _ => (sl σ).2.1) (fun i hi => (hL i hi).1)) ?_
  refine VP.mono (corrSet_vp (P := P) (m := P.W / 2 - 1 - j) (by omega) hD (List.mem_cons_self ..)
    (fun i hi => (hL i hi).2)) (fun σ s ⟨h, p4, p2⟩ => ⟨h, p4, by rw [p2]; rd_up⟩)
    fun σ s h => Dk_congr h (fun e => ?_) (fun e => ?_)
  · have Tl := hT σ e
    have ql := hq σ e
    have g1 := hg σ e
    have d1 := Dq_lt (W := P.W) (m := P.W / 2 - 1 - j) (k := j + 1) (q := q σ) (by omega) mk (hy σ e) (by omega)
      (by omega)
    have fx := fixR_eq (n := j + 2 + 1) (c := dC P.W (AW σ wR) j) (x := q σ) (by omega) Tl
      (fun h0 => hq1 σ e (Nat.le_antisymm g1 (Nat.pos_of_ne_zero h0))) (hc σ e) (by omega)
    simp only [dA, rowV, topW]
    rd_up
    rw [Rs_div.2, Rs_top, sign_val Tl, Dq_win d1.1, corr_row g1 (hq1 σ e) ql, Rs_row Tl (Nat.mod_lt _ (Nat.two_pow_pos _)),
      corr_val Tl, ← fx, upd3_1 (i := wR) (k := wD) (l := wE) (by decide) (by decide), Dq_set ql,
      upd3_2 (i := wR) (k := wD) (l := wE) (by decide)]
    have h1 := hq1 σ e
    generalize T σ / 2 ^ (32 * (j + 2 + 1) - 1) = g at g1 h1 ⊢
    congr 3
    omega
  · simp only [dA, topW]
    rd_up
    rw [upd_upd, Rs_top, sign_val (hT σ e)]
    have h1 := hq1 σ e; have g1 := hg σ e; have := hq σ e
    generalize T σ / 2 ^ (32 * (j + 2 + 1) - 1) = g at g1 h1 ⊢
    congr 1
    omega

/-- `D := 2 s'` after the corrections, from `D'` and `q`. -/
theorem Dv_succ {W x j : Nat} (hj : j + 1 ≤ W / 2) (h : sJ W x j * 2 ^ 32 + dQ W x j = sJ W x (j + 1)) :
    Dv W x (j + 1) = 2 ^ (32 * (W / 2 - 1 - j)) * (2 * sJ W x j * 2 ^ 32 + 2 * dQ W x j) := by
  simp only [Dv]; rw [← h, show W / 2 - (j + 1) = W / 2 - 1 - j by omega]; congr 1; ring

/-- The count `n` at `sK`, as the loop's `cntNext` takes it. -/
theorem KS_withK {σ s : State} {A AW Vf : Nat → Nat} {L LW LS : List Nat} {n : Nat}
    (h : KS P σ A L AW LW Vf LS s) (hK : sK ∈ LS) (v : Vf sK = n) : KS P σ A L AW LW (upd Vf sK n) (sK :: LS) s := by
  rw [upd_noop v]
  exact h.mono (fun i hi => ⟨hi, rfl⟩) (fun i hi => ⟨hi, rfl⟩) fun d hd =>
    ⟨by rcases List.mem_cons.mp hd with rfl | hd; exacts [hK, hd], rfl⟩

/-- A digit. -/
theorem sqDigit_vp {k K : Nat} (hKW : 2 * K + 2 = P.W) (hk : k < K) {L LW LS : List Nat} {E : State → Prop}
    {A AW V : State → Nat → Nat}
    (hR : wR ∈ LW) (hD : wD ∈ LW) (hE : wE ∈ LW)
    (hL : ∀ i ∈ L, i / 2 ≠ wR ∧ i / 2 ≠ wD ∧ i / 2 ≠ wE)
    (hLS : ∀ d ∈ LS, d ≠ sU0 ∧ d ≠ sU2 ∧ (d + 4 ≤ sMk ∨ sMk + 4 ≤ d) ∧ (d + 4 ≤ sQ ∨ sQ + 4 ≤ d))
    (hLn : sLn ∈ LS) (hPo : sPo ∈ LS) (hMo : sMo ∈ LS) (hCm : sCm ∈ LS) (hDs : sD ∈ LS)
    (hD1 : sD1 ∈ LS) (hVs : sV ∈ LS) (hKs : sK ∈ LS)
    (x1 : ∀ σ, E σ → 2 ^ (32 * P.W - 2) ≤ AW σ wR) (x2 : ∀ σ, E σ → AW σ wR < 2 ^ (32 * P.W))
    (vD : ∀ σ, E σ → V σ sD = sJ P.W (AW σ wR) 1) (vV : ∀ σ, E σ → V σ sV = (2 ^ 64 - 1) / V σ sD - 2 ^ 32) :
    VP (fun σ s => E σ ∧ Dk P E A L (fun σ => DAW P.W (k + 1) (AW σ)) LW
        (fun σ => DV P.W K (k + 1) (sJ P.W (AW σ wR) (k + 1)) (V σ)) LS P.W 22 σ s) sqDigit
      (fun σ s => (E σ ∧ Dk P E A L (fun σ => DAW P.W (k + 1 + 1) (AW σ)) LW
        (fun σ => DV P.W K (k + 1 + 1) (sJ P.W (AW σ wR) (k + 1 + 1)) (V σ)) LS P.W 22 σ s) ∧
        s.z = decide (K - (k + 1) = 0)) := by
  generalize hj : k + 1 = j
  have j1 : 1 ≤ j := by omega
  have hjW : 2 * j + 2 ≤ P.W := by omega
  refine VP.of_imp (p := P.W ≤ 518) (fun σ s h => h.2.2.1.sizes.Wle) fun Wl => ?_
  have mth := fun σ (e : E σ) => dig_math (x1 σ e) (x2 σ e) j1 hjW
  have Pl : ∀ σ, pairP P.W (AW σ wR) j < 2 ^ 64 := fun σ => Nat.mod_lt _ (by decide)
  have bd := fun σ (e : E σ) {y : Nat} (hy : y ≤ 2 ^ 32 + 1) =>
    dig_bounds (j := j) (mth σ e).1.2 (mth σ e).2.1 (Pl σ) hy
  have eK : ∀ σ, E σ → (DV P.W K j (sJ P.W (AW σ wR) j) (V σ)) sD * 2 ^ 32 +
      (DV P.W K j (sJ P.W (AW σ wR) j) (V σ)) sD1 = sJ P.W (AW σ wR) j * 2 ^ 32 / 2 ^ (32 * (j - 1)) := fun σ e => by
    rd_up; rw [vD σ e, ← (mth σ e).2.2.2.2.2.2.2.2.2.2.2.2]; omega
  have eD : ∀ σ, E σ → (DV P.W K j (sJ P.W (AW σ wR) j) (V σ)) sD =
      sJ P.W (AW σ wR) j * 2 ^ 32 / 2 ^ (32 * (j - 1)) / 2 ^ 32 := fun σ e => by
    rd_up; rw [vD σ e, ← (mth σ e).2.2.2.2.2.2.2.2.2.2.2.2]
  have eP : ∀ σ, dR P.W (AW σ wR) j / 2 ^ (32 * (j - 1) + 1) = dR P.W (AW σ wR) j / (2 * 2 ^ (32 * (j - 1))) :=
    fun σ => by rw [Nat.pow_succ, Nat.mul_comm (2 ^ _)]
  have sD0 : ∀ σ, E σ → 0 < sJ P.W (AW σ wR) j * 2 ^ 32 / 2 ^ (32 * (j - 1)) / 2 ^ 32 := fun σ e => by
    rw [(mth σ e).2.2.2.2.2.2.2.2.2.2.2.2]
    have := (sJ_bounds (j := 1) (x1 σ e) (x2 σ e) (le_refl _) (by omega)).1
    exact Nat.lt_of_lt_of_le (Nat.two_pow_pos _) this
  have hQb : ∀ σ, dQh P.W (AW σ wR) j < 2 ^ 32 := fun σ => Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by decide)
  have yl : ∀ σ, E σ → 2 * sJ P.W (AW σ wR) j < 2 ^ (32 * (j + 1)) := fun σ e => by
    have := (mth σ e).1.2
    have : (2 : Nat) ^ (32 * (j + 1)) = 2 ^ (32 * j) * 2 ^ 32 := by rw [pow32_add, Nat.mul_one]
    omega
  have mk : P.W / 2 - 1 - j + (j + 1) + 1 ≤ P.W := by omega
  have dl := fun σ (e : E σ) {q : Nat} (hq : q < 2 ^ 33) =>
    Dq_lt (W := P.W) (m := P.W / 2 - 1 - j) (q := q) (by omega) mk (yl σ e) (by omega) hq
  have rl : ∀ σ, E σ → dR P.W (AW σ wR) j < 2 ^ (32 * (j + 2 + 1)) := fun σ e =>
    (bd σ e (y := 0) (by decide)).2.2.2.1
  have rl2 : ∀ σ, E σ → dR P.W (AW σ wR) j < 2 ^ (32 * (j + 2) + 1) := fun σ e => by
    have r1 := (bd σ e (y := 0) (by decide)).2.2.2.2.2
    have e1 : (2 : Nat) ^ (32 * (j + 2) + 1) = 2 ^ (32 * j + 1) * 2 ^ 64 := by rw [← Nat.pow_add]; congr 1
    have hm := Nat.mul_le_mul_right (2 ^ 64) (show rJ P.W (AW σ wR) j + 1 ≤ 2 ^ (32 * j + 1) by omega)
    have := Pl σ
    simp only [dR]; rw [e1]; rw [Nat.add_mul, Nat.one_mul] at hm; omega
  have mQ : ∀ {d}, d ∈ LS → d ∈ sQ :: LS := fun h => List.mem_cons_of_mem _ h
  have sl := fun (σ : State) (q : Nat) => dSlots (sw := sJ P.W (AW σ wR) j) (q := q) (v := V σ) (K := K) hjW hKW Wl
  have hR0 : ∀ σ, dA P.W j (AW σ) (dR P.W (AW σ wR) j) 0 0 wR / 2 ^ (32 * (P.W - 2 * j - 2)) = dR P.W (AW σ wR) j :=
    fun σ => by simp only [dA]; rd_up; exact Rs_div.2
  -- the arrays in the digit's terms
  refine VP.mono (F := Dk P E A L (fun σ => dA P.W j (AW σ) (dR P.W (AW σ wR) j) 0 0) LW
    (fun σ => DV P.W K j (sJ P.W (AW σ wR) j) (V σ)) LS P.W 22) ?_
    (fun σ s h => Dk_congr h.2 (fun _ => by simp only [DAW, dA]; rw [Rv_Rs hjW, Dv_Dq (by omega)]) (fun _ => rfl))
    (fun _ _ h => h)
  simp only [sqDigit, mulSubD, seqs]
  -- the estimate
  refine VP.seq (ptrSlot_vp (P := P) (rb := .r10) (by decide) (j := wR) (d := sPo) (i := P.W - 2 * j - 2) (by decide) hPo
    (fun σ e => by rd_up; omega) estPtr_taint) ?_
  refine VP.seq (estOff_vp (P := P) (k := arr P.W wR) (i := P.W - 2 * j - 2) (i' := j) hMo (fun σ e => by rd_up)) ?_
  refine VP.seq (G := dStage P E A L AW V LW LS K j (fun σ => dR P.W (AW σ wR) j) (fun _ => 0) (fun _ => 0)
      (fun σ => dQh P.W (AW σ wR) j))
    (dk_post (est_vp (P := P) (ar := wR) (o := P.W - 2 * j - 2) (m := j) j1 (by omega) hR hLS hDs hD1 hVs
      (fun σ e => by
        have := (sJ_bounds (j := 1) (x1 σ e) (x2 σ e) (le_refl _) (by omega)).1
        rd_up; rw [vD σ e]; exact this)
      (fun σ e => by rd_up; exact vV σ e)
      (fun σ e => by rw [hR0]; exact rl2 σ e)
      (fun σ e => by rw [hR0, eD σ e, eP σ]; exact (mth σ e).2.2.2.2.2.2.1)
      (fun σ e => by rw [hR0, eK σ e, eP σ]; exact (mth σ e).2.2.2.2.2.2.2.1)
      (fun σ e => by
        rw [hR0, eK σ e, eD σ e, quot_min (sD0 σ e) (by rw [eP σ]; exact (mth σ e).2.2.2.2.2.2.1), eP σ]
        have h := (mth σ e).2.2.2.2.2.2.2.2.1; unfold dQh at h; rw [eP σ] at h; exact h)
      (fun σ e => by
        rw [hR0, eK σ e, eD σ e, quot_min (sD0 σ e) (by rw [eP σ]; exact (mth σ e).2.2.2.2.2.2.1), eP σ]
        have h := (mth σ e).2.2.2.2.2.2.2.2.2.1; unfold dQh at h; rw [eP σ] at h; exact h))
      (fun _ _ => rfl) (fun σ e => by rw [hR0, eK σ e])) ?_
  -- `q̂` into `D'` and `C'`, and `T = R - q̂ D'`
  refine VP.seq (G := dStage P E A L AW V LW LS K j
      (fun σ => twos (2 ^ (32 * (j + 2 + 1))) ((dR P.W (AW σ wR) j : Int) -
        ((dC P.W (AW σ wR) j + dQh P.W (AW σ wR) j) * dQh P.W (AW σ wR) j : Nat)))
      (fun σ => dQh P.W (AW σ wR) j) (fun σ => dQh P.W (AW σ wR) j) (fun σ => dQh P.W (AW σ wR) j)) ?_ ?_
  · refine VP.seq (ldCm_vp (P := P) (r := .r3) (by decide) (m := P.W / 2 - 1 - j) (mQ hCm) (fun σ _ => (sl σ _).2.1)
      ldCm3_taint) ?_
    refine VP.seq (G := dStage P E A L AW V LW LS K j (fun σ => dR P.W (AW σ wR) j) (fun σ => dQh P.W (AW σ wR) j)
        (fun σ => dQh P.W (AW σ wR) j) (fun σ => dQh P.W (AW σ wR) j))
      (dk_post (setQ_vp (P := P) (m := P.W / 2 - 1 - j) (by omega) hD hE (List.mem_cons_self ..)
        (fun i hi => ⟨(hL i hi).2.1, (hL i hi).2.2⟩)) (fun σ e => ?_) (fun _ _ => rfl)) ?_
    · simp only [dA]; rd_up
      rw [Dq_set (by decide), C_set (by omega) (dl σ e (q := 0) (by decide)).2 (by decide) (hQb σ),
        upd3_2 (i := wR) (k := wD) (l := wE) (by decide), upd3_3]
    refine VP.seq (dPtrs_vp (P := P) (d := wE) (b := P.W - 2 * j - 2) (m := P.W / 2 - 1 - j) (n := j + 2) (by decide)
      (mQ hPo) (mQ hCm) (mQ hLn) (fun σ _ => (sl σ _).1) (fun σ _ => (sl σ _).2.1) (fun σ _ => (sl σ _).2.2.1)
      (by omega) ptrsE_taint) ?_
    refine dk_post (msRow_vp (P := P) (b := P.W - 2 * j - 2) (m := P.W / 2 - 1 - j) (n := j + 2) (by omega) (by omega)
      (by omega) hR hE (List.mem_cons_self ..) (fun i hi => (hL i hi).1)) (fun σ e => ?_) (fun _ _ => rfl)
    have d1 := dl σ e (q := dQh P.W (AW σ wR) j) (by have := hQb σ; omega)
    simp only [dA, rowV]
    rd_up
    rw [Rs_div.2, Rs_top, C_win (by omega) d1.2 d1.1, Rs_row (rl σ e) (Nat.mod_lt _ (Nat.two_pow_pos _)),
      ms_val (hQb σ) d1.1 (rl σ e), upd3_1 (i := wR) (k := wD) (l := wE) (by decide) (by decide)]
  -- the corrections
  have fs1 := fun σ (e : E σ) => fix_step (n := j + 2 + 1) (R := dR P.W (AW σ wR) j) (c := dC P.W (AW σ wR) j)
    (q := dQ P.W (AW σ wR) j) (x := dQh P.W (AW σ wR) j) (by omega) (hQb σ) (mth σ e).2.2.2.2.1.1
    (mth σ e).2.2.2.2.1.2 (mth σ e).2.2.2.2.2.2.2.2.2.2.1 (mth σ e).2.2.2.2.2.2.2.2.2.2.2.1
    (bd σ e (y := 0) (by decide)).1
    (bd σ e (y := dQ P.W (AW σ wR) j + 2) (by have := (mth σ e).2.2.2.1; omega)).2.1
    (bd σ e (y := dQh P.W (AW σ wR) j) (by have := hQb σ; omega)).2.2.1
  have xl : ∀ σ, E σ → dQ P.W (AW σ wR) j ≤ dX P.W (AW σ wR) j ∧ dX P.W (AW σ wR) j ≤ dQ P.W (AW σ wR) j + 1 :=
    fun σ e => by
      have := (mth σ e).2.2.2.2.2.2.2.2.2.2.1; have := (mth σ e).2.2.2.2.2.2.2.2.2.2.2.1
      simp only [dX]; split <;> omega
  have xb : ∀ σ, dX P.W (AW σ wR) j < 2 ^ 32 := fun σ => Nat.lt_of_le_of_lt (Nat.sub_le _ _) (hQb σ)
  have fs2 := fun σ (e : E σ) => fix_step (n := j + 2 + 1) (R := dR P.W (AW σ wR) j) (c := dC P.W (AW σ wR) j)
    (q := dQ P.W (AW σ wR) j) (x := dX P.W (AW σ wR) j) (by omega) (xb σ) (mth σ e).2.2.2.2.1.1
    (mth σ e).2.2.2.2.1.2 (xl σ e).1 (by have := (xl σ e).2; omega)
    (bd σ e (y := 0) (by decide)).1
    (bd σ e (y := dQ P.W (AW σ wR) j + 2) (by have := (mth σ e).2.2.2.1; omega)).2.1
    (bd σ e (y := dX P.W (AW σ wR) j) (by have := (xl σ e).2; have := (mth σ e).2.2.2.1; omega)).2.2.1
  have bq : ∀ σ, E σ → dX P.W (AW σ wR) j - (if dQ P.W (AW σ wR) j < dX P.W (AW σ wR) j then 1 else 0) =
      dQ P.W (AW σ wR) j := fun σ e => by have := xl σ e; split <;> omega
  have rr : ∀ σ, E σ → twos (2 ^ (32 * (j + 2 + 1)))
      ((dR P.W (AW σ wR) j : Int) - ((dC P.W (AW σ wR) j + dQ P.W (AW σ wR) j) * dQ P.W (AW σ wR) j : Nat)) =
      rJ P.W (AW σ wR) (j + 1) := fun σ e => by
    rw [← Nat.cast_sub (mth σ e).2.2.2.2.1.1, ← (mth σ e).2.2.2.2.2.1, twos_nat]
    exact Nat.lt_of_le_of_lt (by rw [(mth σ e).2.2.2.2.2.1]; exact Nat.sub_le _ _) (rl σ e)
  have hL2 : ∀ i ∈ L, i / 2 ≠ wR ∧ i / 2 ≠ wD := fun i hi => ⟨(hL i hi).1, (hL i hi).2.1⟩
  refine VP.seq (G := dStage P E A L AW V LW LS K j
      (fun σ => twos (2 ^ (32 * (j + 2 + 1))) ((dR P.W (AW σ wR) j : Int) -
        ((dC P.W (AW σ wR) j + dX P.W (AW σ wR) j) * dX P.W (AW σ wR) j : Nat)))
      (fun σ => dX P.W (AW σ wR) j) (fun σ => dQh P.W (AW σ wR) j) (fun σ => dX P.W (AW σ wR) j))
    (dk_post (correct_vp j1 hjW hKW hR hD hL2 hLn hPo hCm yl (fun σ _ => twos_lt _ _)
      (fun σ e => by rw [(fs1 σ e).1]; split <;> omega)
      (fun σ e h => by rw [(fs1 σ e).1] at h; split at h <;> omega) (fun σ _ => hQb σ)
      (fun σ e => (bd σ e (y := dQh P.W (AW σ wR) j) (by have := hQb σ; omega)).2.2.1))
      (fun σ e => by beta_reduce; rw [(fs1 σ e).2, (fs1 σ e).1]) (fun σ e => by beta_reduce; rw [(fs1 σ e).1])) ?_
  refine VP.seq (G := dStage P E A L AW V LW LS K j (fun σ => rJ P.W (AW σ wR) (j + 1))
      (fun σ => dQ P.W (AW σ wR) j) (fun σ => dQh P.W (AW σ wR) j) (fun σ => dQ P.W (AW σ wR) j))
    (dk_post (correct_vp j1 hjW hKW hR hD hL2 hLn hPo hCm yl (fun σ _ => twos_lt _ _)
      (fun σ e => by rw [(fs2 σ e).1]; split <;> omega)
      (fun σ e h => by rw [(fs2 σ e).1] at h; split at h <;> omega) (fun σ _ => xb σ)
      (fun σ e => (bd σ e (y := dX P.W (AW σ wR) j) (by have := (xl σ e).2; have := (mth σ e).2.2.2.1; omega)).2.2.1))
      (fun σ e => by beta_reduce; rw [(fs2 σ e).2, (fs2 σ e).1, bq σ e, rr σ e])
      (fun σ e => by beta_reduce; rw [(fs2 σ e).1, bq σ e])) ?_
  -- `D := 2 s'`
  refine VP.seq (ldCm_vp (P := P) (r := .r1) (by decide) (m := P.W / 2 - 1 - j) (mQ hCm) (fun σ _ => (sl σ _).2.1)
      ldCm1_taint) ?_
  refine VP.seq (G := Dk P E A L (fun σ => DAW P.W (j + 1) (AW σ)) LW
      (fun σ => upd (DV P.W K j (sJ P.W (AW σ wR) j) (V σ)) sQ (dQ P.W (AW σ wR) j)) (sQ :: LS) P.W 22)
      (dk_post (finishQ_vp (P := P) (m := P.W / 2 - 1 - j) (by omega) hD hE (List.mem_cons_self ..)
        (fun i hi => ⟨(hL i hi).2.1, (hL i hi).2.2⟩)) (fun σ e => ?_) (fun _ _ => rfl)) ?_
  · have ql := (mth σ e).2.2.2.1
    simp only [dA, DAW]; rd_up
    have y2 : 2 * sJ P.W (AW σ wR) j % 2 = 0 := by omega
    rw [Dq_finish (m := P.W / 2 - 1 - j) ql y2,
      C_finish (m := P.W / 2 - 1 - j) (k := j + 1) (by omega) mk (yl σ e) y2 ql (hQb σ) (by omega),
      upd3_2 (i := wR) (k := wD) (l := wE) (by decide), upd3_3, Rv_succ hjW, Dv_succ (by omega) (mth σ e).2.2.1]
  refine VP.seq (finishD1_vp (P := P) (by omega) hD) ?_
  have m2 : ∀ {d}, d ∈ LS → d ∈ sD1 :: sQ :: LS := fun h => List.mem_cons_of_mem _ (mQ h)
  refine VP.seq (digNext_vp (P := P) (po := 4 * (P.W - 2 * j - 2)) (mo := 4 * j) (ln := j + 2 + 1)
    (cm := 4 * (P.W / 2 - 1 - j)) (m2 hPo) (m2 hMo) (m2 hLn) (m2 hCm) (fun σ e => by rd_up; omega)
    (fun σ e => by rd_up) (fun σ e => by rd_up) (fun σ e => by rd_up; omega) (by omega) (by omega)) ?_
  -- the count
  refine VP.dctx cntNext_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hv⟩ => ?_
  have h1 := KS_withK (n := K - k) h (m2 hKs) (by rd_up; omega)
  refine WP.mono (cntNext_ok hk (show K < 2 ^ 32 by omega) h1 hv) fun t ⟨⟨ht, hvt⟩, z⟩ => ?_
  refine ⟨⟨e, e, ht.mono (fun i hi => ⟨hi, rfl⟩) (fun i hi => ⟨hi, rfl⟩)
    (fun d hd => ⟨List.mem_cons_of_mem _ (m2 hd), ?_⟩), hvt⟩, by rw [z, hj]⟩
  have hd5 := hLS d hd
  have cQ : d ≠ sQ := fun h0 => by rw [h0] at hd5; omega
  by_cases c1 : d = sK
  · subst c1; rd_up; omega
  · by_cases c2 : d = sLn
    · subst c2; rd_up
    · by_cases c3 : d = sMo
      · subst c3; rd_up; omega
      · by_cases c4 : d = sPo
        · subst c4; rd_up; omega
        · by_cases c6 : d = sCm
          · subst c6; rd_up
            generalize P.W = W at hKW hjW Wl ⊢
            omega
          · by_cases c5 : d = sD1
            · subst c5; rd_up
              simp only [Dv]
              rw [show P.W / 2 - 2 = P.W / 2 - (j + 1) + (j - 1) by omega,
                show P.W / 2 - 1 = P.W / 2 - (j + 1) + (j - 1 + 1) by omega, mul_pow_div, mul_pow_div, d1_val,
                Nat.add_sub_cancel, mul_two32_div j1]
            · simp only [upd_ne _ _ c1, upd_ne _ _ c2, upd_ne _ _ c3, upd_ne _ _ c4, upd_ne _ _ c5, upd_ne _ _ c6,
                upd_ne _ _ cQ]

end

section
variable {P : RP}
open VG.Impl.Rsa.Arm.KeyDiv (sD sV)
open VG.Spec.Rsa (isqrt)

/-- `recip`: `v = ⌊(β² - 1) / d⌋ - β` for `d` (at `sD`) normalized. -/
theorem recip_vp {L LW LS : List Nat} {E : State → Prop} {A AW V : State → Nat → Nat}
    (hD : sD ∈ LS) (vd : ∀ σ, E σ → 2 ^ 31 ≤ V σ sD) :
    VP (Dk P E A L AW LW V LS P.W 22) VG.Impl.Rsa.Arm.KeyDiv.recip
      (Dk P E A L AW LW (fun σ => upd (V σ) sV ((2 ^ 64 - 1) / V σ sD - 2 ^ 32)) (sV :: LS) P.W 22) :=
  VP.dctx recip_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hv⟩ => by
    have dl : V σ sD < 2 ^ 32 := by rw [← h.sl sD hD]; exact BitVec.isLt _
    refine WP.mono (VG.Proof.Rsa.Arm.KeyDiv.recip_ok hv (h.sl sD hD) (vd σ e) dl) fun t ⟨eV, k, r⟩ =>
      ⟨e, h.slot1 k (by decide) (by rw [r.gpr _ (by decide), h.r8]) r.sp r.rd r.wr eV,
        hv.of (r.gpr _ (by decide)) (r.gpr _ (by decide)) (r.gpr _ (by decide)) r.wr⟩

theorem setWin_top2 {x o v W : Nat} (h : o + 2 = W) (hx : x < 2 ^ (32 * W)) :
    setWin x o 2 v = x % 2 ^ (32 * o) + 2 ^ (32 * o) * v := by
  show x % 2 ^ (32 * o) + 2 ^ (32 * o) * (v + 2 ^ (32 * 2) * (x / 2 ^ (32 * (o + 2)))) = _
  rw [Nat.div_eq_of_lt (by rw [h]; exact hx), Nat.mul_zero, Nat.add_zero]

theorem setWin_zero {o n v : Nat} : setWin 0 o n v = 2 ^ (32 * o) * v := by
  show 0 % 2 ^ (32 * o) + 2 ^ (32 * o) * (v + 2 ^ (32 * n) * (0 / 2 ^ (32 * (o + n)))) = _
  simp only [Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.zero_add]

/-- The first digit: `D` zero and `C` all ones, the root and remainder of `X'`'s top two words, `D = 2 s₁`
from word `W / 2 - 1` and `C` its complement, `d = s₁` and its reciprocal. -/
theorem firstDigit_vp {L LW LS : List Nat} {E : State → Prop} {A AW V : State → Nat → Nat}
    (hR : wR ∈ LW) (hZ : wZ ∈ LW) (hOne : wOne ∈ LW) (hL : ∀ i ∈ L, i / 2 ≠ wR ∧ i / 2 ≠ wD ∧ i / 2 ≠ wE)
    (z0 : ∀ σ, E σ → AW σ wZ = 0) (o1 : ∀ σ, E σ → AW σ wOne = 1)
    (x1 : ∀ σ, E σ → 2 ^ (32 * P.W - 2) ≤ AW σ wR) (x2 : ∀ σ, E σ → AW σ wR < 2 ^ (32 * P.W)) (W4 : 4 ≤ P.W) :
    VP (Dk P E A L AW LW V LS P.W 22) firstDigit
      (Dk P E A L (fun σ => DAW P.W 1 (AW σ)) (wE :: wD :: LW)
        (fun σ => upd (upd (V σ) sD (sJ P.W (AW σ wR) 1)) sV ((2 ^ 64 - 1) / sJ P.W (AW σ wR) 1 - 2 ^ 32))
        (sV :: sD :: LS) P.W 22) := by
  simp only [firstDigit, seqs]
  refine VP.seq (copyW_vp (o := wD) (a := wZ) (by decide) hZ (by decide) (fun i hi => (hL i hi).2.1) copyDZw_taint) ?_
  refine VP.seq (VP.mono (subW_vp (o := wE) (a := wZ) (b := wOne) (by decide) (List.mem_cons_of_mem _ hZ)
    (List.mem_cons_of_mem _ hOne) (by decide) (by decide) (fun i hi => (hL i hi).2.2) subEZOne_taint)
    (fun _ _ h => h) fun _ _ h => h.1) ?_
  refine VP.seq (isqTop_vp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hR))
    (List.mem_cons_of_mem _ (List.mem_cons_self ..)) (List.mem_cons_self ..)
    (fun σ e => by rd_up; exact z0 σ e) (fun σ e => by
      rd_up; rw [z0 σ e, o1 σ e]; unfold sub32 cmpl
      have := Nat.two_pow_pos (32 * P.W); rw [Nat.mod_eq_of_lt (by omega)]; omega) hL) ?_
  refine dk_post (recip_vp (List.mem_cons_self ..) fun σ e => by
      rd_up; exact (sJ_bounds (j := 1) (x1 σ e) (x2 σ e) (le_refl _) (by omega)).1) (fun σ e => ?_) (fun σ e => ?_)
  · simp only [DAW, Rv, Dv, rJ, sJ, topA, topT, Nat.mul_one]
    rd_up
    rw [setWin_top2 (show P.W - 2 + 2 = P.W by omega) (x2 σ e), setWin_zero]
    funext z
    simp only [Keys.upd]
    split_ifs <;> rfl
  · rd_up
end

/-! ## The loop, its slots and the finish -/

section
variable {P : RP}
open VG.Impl.Rsa.Arm.KeyDiv (sD sD1 sV sQ sMk sU0 sU2)

/-- The digits: `K` of them, from the first digit's root and remainder to `X`'s. -/
theorem sqLoop_vp {K : Nat} (hKW : 2 * K + 2 = P.W) (hK : 0 < K) {L LW LS : List Nat} {E : State → Prop}
    {A AW V : State → Nat → Nat}
    (hR : wR ∈ LW) (hD : wD ∈ LW) (hE : wE ∈ LW)
    (hL : ∀ i ∈ L, i / 2 ≠ wR ∧ i / 2 ≠ wD ∧ i / 2 ≠ wE)
    (hLS : ∀ d ∈ LS, d ≠ sU0 ∧ d ≠ sU2 ∧ (d + 4 ≤ sMk ∨ sMk + 4 ≤ d) ∧ (d + 4 ≤ sQ ∨ sQ + 4 ≤ d))
    (hLn : sLn ∈ LS) (hPo : sPo ∈ LS) (hMo : sMo ∈ LS) (hCm : sCm ∈ LS) (hDs : sD ∈ LS)
    (hD1 : sD1 ∈ LS) (hVs : sV ∈ LS) (hKs : sK ∈ LS)
    (x1 : ∀ σ, E σ → 2 ^ (32 * P.W - 2) ≤ AW σ wR) (x2 : ∀ σ, E σ → AW σ wR < 2 ^ (32 * P.W))
    (vD : ∀ σ, E σ → V σ sD = sJ P.W (AW σ wR) 1) (vV : ∀ σ, E σ → V σ sV = (2 ^ 64 - 1) / V σ sD - 2 ^ 32) :
    VP (fun σ s => E σ ∧ Dk P E A L (fun σ => DAW P.W (0 + 1) (AW σ)) LW
        (fun σ => DV P.W K (0 + 1) (sJ P.W (AW σ wR) (0 + 1)) (V σ)) LS P.W 22 σ s) (.loop sqDigit .ne)
      (fun σ s => E σ ∧ Dk P E A L (fun σ => DAW P.W (K + 1) (AW σ)) LW
        (fun σ => DV P.W K (K + 1) (sJ P.W (AW σ wR) (K + 1)) (V σ)) LS P.W 22 σ s) :=
  VP.count (E := E) (I := fun k σ s => Dk P E A L (fun σ => DAW P.W (k + 1) (AW σ)) LW
      (fun σ => DV P.W K (k + 1) (sJ P.W (AW σ wR) (k + 1)) (V σ)) LS P.W 22 σ s) hK fun _ hk =>
    sqDigit_vp hKW hk hR hD hE hL hLS hLn hPo hMo hCm hDs hD1 hVs hKs x1 x2 vD vV

/-- The digits' slots. -/
theorem sqInit_vp {L LW LS : List Nat} {E : State → Prop} {A AW V : State → Nat → Nat} :
    VP (Dk P E A L AW LW V LS P.W 22) (.block sqInit)
      (Dk P E A L AW LW (fun σ => upd (upd (upd (upd (upd (upd (V σ) sPo (4 * P.W - 16)) sMo 4)
        sK ((P.W - 2) / 2)) sLn 4) sD1 0) sCm (2 * P.W - 8))
        (sCm :: sD1 :: sLn :: sK :: sMo :: sPo :: LS) P.W 22) :=
  VP.dctx sqInit_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hv⟩ => by
    have Wl := h.sizes.Wle
    have W4 : 4 ≤ P.W := by simp only [RP.W, RP.w]; omega
    unfold sqInit
    refine wp_mov (op2_lsl (by decide)) fun s1 u1 => ?_
    obtain ⟨h1, hv1⟩ := h.reg hv (u1.rest (ws := [.r1]) (by simp)) u1.mem
    refine wp_dp (op2_imm (by decide)) fun s2 u2 => ?_
    obtain ⟨h2, hv2⟩ := h1.reg hv1 (u2.rest (ws := [.r1]) (by simp)) u2.mem
    refine h2.strSlot hv2 (d := sPo) (r := .r1) (by decide) fun s3 h3 hv3 g3 _ => ?_
    refine wp_mov (op2_imm (by decide)) fun s4 u4 => ?_
    obtain ⟨h4, hv4⟩ := h3.reg hv3 (u4.rest (ws := [.r1]) (by simp)) u4.mem
    refine h4.strSlot hv4 (d := sMo) (r := .r1) (by decide) fun s5 h5 hv5 g5 _ => ?_
    refine wp_dp (op2_imm (by decide)) fun s6 u6 => ?_
    obtain ⟨h6, hv6⟩ := h5.reg hv5 (u6.rest (ws := [.r1]) (by simp)) u6.mem
    refine wp_mov (op2_lsr (by decide)) fun s7 u7 => ?_
    obtain ⟨h7, hv7⟩ := h6.reg hv6 (u7.rest (ws := [.r1]) (by simp)) u7.mem
    refine h7.strSlot hv7 (d := sK) (r := .r1) (by decide) fun s8 h8 hv8 g8 _ => ?_
    refine wp_mov (op2_imm (by decide)) fun s9 u9 => ?_
    obtain ⟨h9, hv9⟩ := h8.reg hv8 (u9.rest (ws := [.r1]) (by simp)) u9.mem
    refine h9.strSlot hv9 (d := sLn) (r := .r1) (by decide) fun s10 h10 hv10 g10 _ => ?_
    refine wp_mov (op2_imm (by decide)) fun s11 u11 => ?_
    obtain ⟨h11, hv11⟩ := h10.reg hv10 (u11.rest (ws := [.r1]) (by simp)) u11.mem
    refine h11.strSlot hv11 (d := sD1) (r := .r1) (by decide) fun s12 h12 hv12 g12 _ => ?_
    refine wp_mov (op2_lsl (by decide)) fun s13 u13 => ?_
    obtain ⟨h13, hv13⟩ := h12.reg hv12 (u13.rest (ws := [.r1]) (by simp)) u13.mem
    refine wp_dp (op2_imm (by decide)) fun s14 u14 => ?_
    obtain ⟨h14, hv14⟩ := h13.reg hv13 (u14.rest (ws := [.r1]) (by simp)) u14.mem
    refine h14.strSlot hv14 (d := sCm) (r := .r1) (by decide) fun t ht hvt _ _ => WP.block_nil ⟨e, ?_, hvt⟩
    have e2 : (s2.gpr .r1).toNat = 4 * P.W - 16 := by
      rw [u2.gpr, dpVal, u1.gpr, hv.r9, BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (a := P.W) (by omega), Nat.shiftLeft_eq, show (16 : BitVec 32).toNat = 16 from rfl]
      omega
    have e7 : (s7.gpr .r1).toNat = (P.W - 2) / 2 := by
      rw [u7.gpr, u6.gpr, dpVal, hv5.r9, BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (a := P.W) (by omega), show (2 : BitVec 32).toNat = 2 from rfl, Nat.shiftRight_eq_div_pow]
      congr 1; omega
    have e14 : (s14.gpr .r1).toNat = 2 * P.W - 8 := by
      rw [u14.gpr, dpVal, u13.gpr, hv12.r9, BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (a := P.W) (by omega), Nat.shiftLeft_eq, show (8 : BitVec 32).toNat = 8 from rfl]
      omega
    rw [e14, e7, e2, u11.gpr, u9.gpr, u4.gpr] at ht
    exact ht.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨hj, rfl⟩) (fun d hd => ⟨hd, rfl⟩)

/-- The root `s = D / 2` into `[wS]`. -/
theorem sqEnd_vp {L LW LS : List Nat} {E : State → Prop} {A AW V : State → Nat → Nat}
    (hD : wD ∈ LW) (hL : ∀ i ∈ L, i / 2 ≠ wS) :
    VP (Dk P E A L AW LW V LS P.W 22) sqEnd
      (Dk P E A L (fun σ => upd (AW σ) wS (AW σ wD / 2)) (wS :: LW) V LS P.W 22) := by
  simp only [sqEnd, seqs]
  refine VP.seq (copyW_vp (o := wS) (a := wD) (by decide) hD (by decide) hL copySD_taint) ?_
  refine VP.seq (G := fun σ s => Dk P E A L (fun σ => upd (AW σ) wS (AW σ wD)) (wS :: LW) V LS P.W 22 σ s ∧
      (s.gpr .r11).toNat = 0)
    (VP.dctx clr11_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hv⟩ =>
      List.append_nil clr11 ▸ h.clr11 hv fun t ht hvt z => WP.block_nil ⟨⟨e, ht, hvt⟩, z⟩) ?_
  refine VP.dctx halfS_taint (fun _ _ h => h.1.2.2) fun σ s ⟨⟨e, h, hv⟩, z⟩ =>
    WP.mono (h.half_W hv (List.mem_cons_self ..) z hL) fun t ⟨ht, hvt, _⟩ => ⟨e, ht.mono (fun i hi => ⟨hi, rfl⟩)
      (fun i hi => ⟨List.mem_cons_of_mem _ hi, ?_⟩) (fun d hd => ⟨hd, rfl⟩), hvt⟩
  rw [upd_upd]; rd_up

/-- `sqMid`: `c = ⌊lz / 2⌋` into `sTu`, the word stages' slots. -/
theorem sqMid_ok {lz : Nat} {σ s : State} {A AW V : Nat → Nat} {L LW LS : List Nat}
    (hS : sLz ∈ LS) (vS : V sLz = lz) (h : KS P σ A L AW LW V LS s) (hv : Ws s P.B P.Z P.W 22) :
    WP isa (.block sqMid) s fun t =>
      KS P σ A L AW LW (WSV (upd V sTu (lz / 2)) (lz / 2 / 32) 0) (LSS (sTu :: LS)) t ∧ Ws t P.B P.Z P.W 22 := by
  have b1 : lz < 2 ^ 32 := by rw [← vS, ← h.sl sLz hS]; exact BitVec.isLt _
  unfold sqMid
  refine h.ldrSlot hv (d := sLz) hS (r := .r1) (by decide) fun s1 h1 hv1 u1 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s2 u2 => ?_
  obtain ⟨h2, hv2⟩ := h1.reg hv1 (u2.rest (ws := [.r1]) (by simp)) u2.mem
  refine h2.strSlot hv2 (d := sTu) (r := .r1) (by decide) fun s3 h3 hv3 g3 _ => ?_
  refine wp_mov (op2_lsr (by decide)) fun s4 u4 => ?_
  obtain ⟨h4, hv4⟩ := h3.reg hv3 (u4.rest (ws := [.r1]) (by simp)) u4.mem
  refine h4.strSlot hv4 (d := sTk) (r := .r1) (by decide) fun s5 h5 hv5 _ _ => ?_
  refine wp_mov (op2_imm (by decide)) fun s6 u6 => ?_
  obtain ⟨h6, hv6⟩ := h5.reg hv5 (u6.rest (ws := [.r1]) (by simp)) u6.mem
  refine h6.strSlot hv6 (d := sWs) (r := .r1) (by decide) fun t ht hvt _ _ => WP.block_nil ⟨?_, hvt⟩
  have e2 : (s2.gpr .r1).toNat = lz / 2 := by
    rw [u2.gpr, u1.gpr, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, vS, Nat.mod_eq_of_lt b1,
      Nat.shiftRight_eq_div_pow]
  have e4 : (s4.gpr .r1).toNat = lz / 2 / 32 := by
    rw [u4.gpr, g3, BitVec.toNat_ushiftRight, e2, Nat.shiftRight_eq_div_pow]
  rw [e4, e2, u6.gpr] at ht
  refine ht.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨hj, rfl⟩) (fun d hd => ⟨hd, ?_⟩)
  simp only [WSV, Nat.pow_zero, Nat.div_one, Nat.mul_one]; rfl

end

section
variable {P : RP}

/-- The root after the bit stages and `m` word stages. -/
abbrev rootW (v lz : State → Nat) (m : Nat) (σ : State) : Nat :=
  v σ / 2 ^ (lz σ / 2 % 32 + 32 * (lz σ / 2 / 32 % 2 ^ m))

/-- `[wG]` after `m` word stages. -/
abbrev rootG (v lz : State → Nat) (m : Nat) (σ : State) : Nat :=
  if m = 0 then v σ / 2 ^ (lz σ / 2 % 2 ^ 4) / 2 ^ (2 ^ 4) else rootW v lz (m - 1) σ / 2 ^ (32 * 2 ^ (m - 1))

/-- The finish: whether the remainder is 0 (`sOk5`), the root shifted down by `c = ⌊lz / 2⌋` bits, 0 where
`X` was 0 (`sZ`), its low `w` words into the narrow `[aY]`. The root's stages run over its `W / 2` words. -/
theorem sqFinish_vp {L LW LS : List Nat} {E : State → Prop} {A AW V : State → Nat → Nat} {v lz z : State → Nat}
    (hS : wS ∈ LW) (hRr : wR ∈ LW) (hZ : wZ ∈ LW)
    (hLWT : ∀ j ∈ LW, j ≠ wG ∧ j ≠ wF ∧ j ≠ 18 ∧ aY / 2 ≠ j)
    (hL : ∀ j ∈ L, j / 2 ≠ wG ∧ j / 2 ≠ wF ∧ j / 2 ≠ wS ∧ j / 2 ≠ 18)
    (hLS : ∀ d ∈ LS, d ≠ sOk5 ∧ d ≠ sTu ∧ d ≠ sTk ∧ d ≠ sWs ∧ d ≠ sBit ∧ d ≠ sK ∧ (d + 4 ≤ sT ∨ sT + 4 ≤ d))
    (hLz : sLz ∈ LS) (hZs : sZ ∈ LS)
    (z0 : ∀ σ, E σ → AW σ wZ = 0) (vS : ∀ σ, E σ → AW σ wS = v σ) (vLz : ∀ σ, E σ → V σ sLz = lz σ)
    (vZ : ∀ σ, E σ → V σ sZ = z σ) (zb : ∀ σ, E σ → z σ ≤ 1) (lzb : ∀ σ, E σ → lz σ < 32 * P.W)
    (bv : ∀ σ, E σ → v σ < 2 ^ (32 * (P.W / 2))) :
    VP (Dk P E A L AW LW V LS P.W 22) sqFinish
      (Dk P E (fun σ => upd (A σ) aY ((if z σ = 0 then v σ / 2 ^ (lz σ / 2) else 0) % 2 ^ (32 * P.w))) (aY :: L)
        (fun σ => upd (upd (AW σ) wS (v σ / 2 ^ (lz σ / 2))) wG (if z σ = 0 then v σ / 2 ^ (lz σ / 2) else 0))
        (wG :: LW) (fun σ => upd (V σ) sOk5 (if AW σ wR = 0 then 1 else 0)) (sOk5 :: LS) P.w nArr) := by
  have bd : ∀ σ, E σ → ∀ k, v σ / k < 2 ^ (32 * (P.W / 2)) := fun σ e _ =>
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (bv σ e)
  have bd2 : ∀ σ, E σ → ∀ k k', v σ / k / k' < 2 ^ (32 * (P.W / 2)) := fun σ e _ _ =>
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (bd σ e _)
  have hS2 : wS ∈ wG :: wF :: LW := List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hS)
  have hZ2 : wZ ∈ wG :: wF :: LW := List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ)
  have hG2 : wG ∈ wG :: wF :: LW := List.mem_cons_self ..
  have hF2 : wF ∈ wG :: wF :: LW := List.mem_cons_of_mem _ (List.mem_cons_self ..)
  have hLB : ∀ j ∈ L, j / 2 ≠ wG ∧ j / 2 ≠ wF ∧ j / 2 ≠ wS := fun j hj => ⟨(hL j hj).1, (hL j hj).2.1, (hL j hj).2.2.1⟩
  simp only [sqFinish, seqs]
  -- whether the remainder is 0
  refine VP.seq (G := Dk P E A L AW LW (fun σ => upd (V σ) sOk5 (if AW σ wR = 0 then 1 else 0)) (sOk5 :: LS)
      P.W 22)
    ((eqSW_vp (d := sOk5) (a := wR) (b := wZ) (t := 18) hRr hZ (by decide) (by decide)
      (fun h => (hLWT 18 h).2.2.1 rfl) (fun j hj => (hL j hj).2.2.2) (fun e he => (hLS e he).2.2.2.2.2.2)
      (by decide) eqOk5W_taint).mono (fun _ _ h => h) fun σ s ⟨e, h, hv⟩ => ⟨e, h.mono (fun j hj => ⟨hj, rfl⟩)
        (fun j hj => ⟨hj, rfl⟩) (fun d hd => ⟨hd, by simp only [z0 σ e]⟩), hv⟩) ?_
  -- `[wG]` and `[wF]` zero
  refine (copyW_vp (o := wG) (a := wZ) (by decide) hZ (by decide) (fun j hj => (hL j hj).1) copyGZ_taint).seq ?_
  refine VP.seq (G := Dk P E A L (fun σ => upd (upd (upd (AW σ) wG 0) wF 0) wS (v σ / 2 ^ (lz σ / 2 % 2 ^ 0)))
      (wG :: wF :: LW) (fun σ => upd (V σ) sOk5 (if AW σ wR = 0 then 1 else 0)) (sOk5 :: LS) P.W 22)
    ((copyW_vp (o := wF) (a := wZ) (by decide) (List.mem_cons_of_mem _ hZ) (by decide) (fun j hj => (hL j hj).2.1)
      copyFZw_taint).mono (fun _ _ h => h) fun σ s ⟨e, h, hv⟩ => ⟨e, h.mono (fun j hj => ⟨hj, rfl⟩)
        (fun j hj => ⟨?_, ?_⟩) (fun d hd => ⟨hd, rfl⟩), hv⟩) ?_
  · simp only [List.mem_cons] at hj ⊢; grind
  · have zG : wZ ≠ wG := by decide
    simp only [Nat.pow_zero, Nat.mod_one, Nat.div_one]
    by_cases c1 : j = wS
    · subst c1; simp only [upd_self, upd_ne _ _ (show wS ≠ wF by decide), upd_ne _ _ (show wS ≠ wG by decide)]
      exact vS σ e
    · by_cases c2 : j = wF
      · subst c2; simp only [upd_self, upd_ne _ _ c1, upd_ne _ _ zG]; exact z0 σ e
      · by_cases c3 : j = wG
        · subst c3; simp only [upd_self, upd_ne _ _ c1, upd_ne _ _ c2]; exact z0 σ e
        · simp only [upd_ne _ _ c1, upd_ne _ _ c2, upd_ne _ _ c3]
  -- `c` and the word stages' slots
  refine VP.seq (G := Dk P E A L (fun σ => upd (upd (upd (AW σ) wG 0) wF 0) wS (v σ / 2 ^ (lz σ / 2 % 2 ^ 0)))
      (wG :: wF :: LW) (fun σ => WSV (upd (upd (V σ) sOk5 (if AW σ wR = 0 then 1 else 0)) sTu
      (lz σ / 2)) (lz σ / 2 / 32) 0) (LSS (sTu :: sOk5 :: LS)) P.W 22)
    (VP.dctx sqMid_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hv⟩ =>
      WP.mono (sqMid_ok (List.mem_cons_of_mem _ hLz) (by rd_up; exact vLz σ e) h hv) fun t ⟨ht, hvt⟩ =>
        ⟨e, ht, hvt⟩) ?_
  -- the bit stages
  have lsB : ∀ d ∈ LSS (sTu :: sOk5 :: LS), d ≠ sBit ∧ d ≠ sK := fun d hd => by
    simp only [LSS, List.mem_cons] at hd
    rcases hd with rfl | rfl | rfl | rfl | hd
    · decide
    · decide
    · decide
    · decide
    · exact ⟨(hLS d hd).2.2.2.2.1, (hLS d hd).2.2.2.2.2.1⟩
  have st : ∀ i, i < 5 → ∀ g f : State → Nat, (∀ σ, E σ → g σ < 2 ^ (32 * (P.W / 2))) →
      (∀ σ, E σ → f σ < 2 ^ (32 * (P.W / 2))) →
      VP (Dk P E A L (fun σ => upd (upd (upd (AW σ) wG (g σ)) wF (f σ)) wS (v σ / 2 ^ (lz σ / 2 % 2 ^ i)))
        (wG :: wF :: LW)
        (fun σ => WSV (upd (upd (V σ) sOk5 (if AW σ wR = 0 then 1 else 0)) sTu (lz σ / 2)) (lz σ / 2 / 32) 0)
        (LSS (sTu :: sOk5 :: LS)) P.W 22) (rootBitStage i)
      (Dk P E A L (fun σ => upd (upd (upd (AW σ) wG (v σ / 2 ^ (lz σ / 2 % 2 ^ i) / 2 ^ (2 ^ i))) wF
          (v σ / 2 ^ (lz σ / 2 % 2 ^ (i + 1)))) wS (v σ / 2 ^ (lz σ / 2 % 2 ^ (i + 1)))) (wG :: wF :: LW)
        (fun σ => WSV (upd (upd (V σ) sOk5 (if AW σ wR = 0 then 1 else 0)) sTu (lz σ / 2)) (lz σ / 2 / 32) 0)
        (LSS (sTu :: sOk5 :: LS)) P.W 22) := fun i hi g f bg bf =>
    (rootBitStage_vp (v := v) (t := fun σ => lz σ / 2) (g := g) (f := f) hi hS2 hG2 hF2 hLB
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      (fun σ _ => by simp only [WSV]; rd_up) bv bg bf).mono (fun _ _ h => h) fun σ s h => drop_scratch lsB h
  refine (st 0 (by decide) (fun _ => 0) (fun _ => 0) (fun _ _ => Nat.two_pow_pos _)
    (fun _ _ => Nat.two_pow_pos _)).seq ?_
  refine (st 1 (by decide) (fun σ => v σ / 2 ^ (lz σ / 2 % 2 ^ 0) / 2 ^ (2 ^ 0))
    (fun σ => v σ / 2 ^ (lz σ / 2 % 2 ^ (0 + 1))) (fun σ e => bd2 σ e _ _) (fun σ e => bd σ e _)).seq ?_
  refine (st 2 (by decide) (fun σ => v σ / 2 ^ (lz σ / 2 % 2 ^ 1) / 2 ^ (2 ^ 1))
    (fun σ => v σ / 2 ^ (lz σ / 2 % 2 ^ (1 + 1))) (fun σ e => bd2 σ e _ _) (fun σ e => bd σ e _)).seq ?_
  refine (st 3 (by decide) (fun σ => v σ / 2 ^ (lz σ / 2 % 2 ^ 2) / 2 ^ (2 ^ 2))
    (fun σ => v σ / 2 ^ (lz σ / 2 % 2 ^ (2 + 1))) (fun σ e => bd2 σ e _ _) (fun σ e => bd σ e _)).seq ?_
  refine (st 4 (by decide) (fun σ => v σ / 2 ^ (lz σ / 2 % 2 ^ 3) / 2 ^ (2 ^ 3))
    (fun σ => v σ / 2 ^ (lz σ / 2 % 2 ^ (3 + 1))) (fun σ e => bd2 σ e _ _) (fun σ e => bd σ e _)).seq ?_
  -- the word stages
  have lsW : ∀ d ∈ sTu :: sOk5 :: LS, d ≠ sBit ∧ d ≠ sTk ∧ d ≠ sWs := fun d hd => by
    simp only [List.mem_cons] at hd
    rcases hd with rfl | rfl | hd
    · decide
    · decide
    · exact ⟨(hLS d hd).2.2.2.2.1, (hLS d hd).2.2.1, (hLS d hd).2.2.2.1⟩
  refine VP.seq (G := fun σ s => E σ ∧ Dk P E A L (fun σ => upd (upd (upd (AW σ) wG (rootG v lz (KWH P) σ)) wF
      (rootW v lz (KWH P) σ)) wS (rootW v lz (KWH P) σ)) (wG :: wF :: LW)
      (fun σ => WSV (upd (upd (V σ) sOk5 (if AW σ wR = 0 then 1 else 0)) sTu (lz σ / 2)) (lz σ / 2 / 32) (KWH P))
      (LSS (sTu :: sOk5 :: LS)) P.W 22 σ s)
    (VP.mono (VP.count (E := E) (I := fun m σ s => Dk P E A L (fun σ => upd (upd (upd (AW σ) wG
        (rootG v lz m σ)) wF (rootW v lz m σ)) wS (rootW v lz m σ)) (wG :: wF :: LW)
        (fun σ => WSV (upd (upd (V σ) sOk5 (if AW σ wR = 0 then 1 else 0)) sTu (lz σ / 2)) (lz σ / 2 / 32) m)
        (LSS (sTu :: sOk5 :: LS)) P.W 22 σ s) (by simp only [KWH]; omega) fun m hm =>
      (rootWordStage_vp (AW0 := AW) (V0 := fun σ => upd (upd (V σ) sOk5 (if AW σ wR = 0 then 1 else 0)) sTu
        (lz σ / 2)) (v := v) (c := fun σ => lz σ / 2 % 32) (q := fun σ => lz σ / 2 / 32)
        (g := rootG v lz m) (f := rootW v lz m) hm hS2 hG2 hF2 hZ2 z0 hLB lsW bv
        (fun σ e => by simp only [rootG]; split <;> exact bd2 σ e _ _) (fun σ e => bd σ e _)).mono
        (fun σ s h => h.2) fun σ s ⟨h, z⟩ => ⟨⟨h.1, h.1, h.2.1.mono (fun j hj => ⟨hj, rfl⟩)
          (fun j hj => ⟨hj, by simp only [rootG, rootW, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]⟩)
          (fun d hd => ⟨hd, rfl⟩), h.2.2⟩, z⟩)
      (fun σ s h => ⟨h.1, h.1, h.2.1.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨hj, ?_⟩) (fun d hd => ⟨hd, rfl⟩),
        h.2.2⟩) (fun _ _ h => h)) ?_
  · simp only [rootG, rootW, ↓reduceIte, Nat.pow_zero, Nat.mod_one, Nat.mul_zero, Nat.add_zero,
      show (2 : Nat) ^ (4 + 1) = 32 from rfl]
  -- the root, or 0 where `X` was 0
  refine VP.seq (VP.mono (selH_vp (o := wG) (a := wS) (b := wZ) (sl := sZ) (by decide) hG2 hS2 hZ2 (by decide)
    (by decide) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZs))))
    (fun σ e => by simp only [WSV]; rd_up; rw [vZ σ e]; exact zb σ e) (fun j hj => (hL j hj).1)
    (fun σ e => by rd_up; exact bd σ e _) (fun σ e => by rd_up; rw [z0 σ e]; exact Nat.two_pow_pos _)
    (fun σ e => by rd_up; simp only [rootG]; split <;> exact bd2 σ e _ _) selGSZH_taint)
    (fun σ s h => h.2) (fun _ _ h => h)) ?_
  refine VP.seq toN_vp ?_
  -- its low words into `[aY]`
  refine VP.dctx copyY22_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hv⟩ => ?_
  have h' := h.narrow (j := wG) (List.mem_cons_self ..) (by decide)
  refine WP.mono (h'.copy_w hv (o := aY) (a := 22) (by decide) (List.mem_cons_self ..) (by decide)
    (fun j hj => ?_)) fun t ⟨ht, hvt, _⟩ => ⟨e, ht.mono (fun j hj => ⟨?_, ?_⟩) (fun j hj => ⟨?_, ?_⟩)
      (fun d hd => ⟨?_, ?_⟩), hvt⟩
  · rcases List.mem_cons.mp hj with rfl | hj
    · decide
    · rcases List.mem_cons.mp hj with rfl | hj
      · decide
      · exact (hLWT j hj).2.2.2
  · rcases List.mem_cons.mp hj with rfl | hj
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hj)
  · have q2 : lz σ / 2 / 32 < 2 ^ KWH P := by
      have := lzb σ e; have := kwh_ge (P := P); have : P.W = 2 * P.w + 2 := rfl; omega
    have et : lz σ / 2 % 32 + 32 * (lz σ / 2 / 32 % 2 ^ KWH P) = lz σ / 2 := by rw [Nat.mod_eq_of_lt q2]; omega
    by_cases c : j = aY
    · subst c; simp only [show 2 * wG = 22 from rfl, WSV, rootW]; rd_up; rw [et, vZ σ e, z0 σ e]
    · have c2 : j ≠ 22 := fun h0 => by
        rcases List.mem_cons.mp hj with h1 | h1
        · exact c h1
        · have := (hL j h1).1; rw [h0] at this; exact this rfl
      simp only [show 2 * wG = 22 from rfl, upd_ne _ _ c, upd_ne _ _ c2]
  · rcases List.mem_cons.mp hj with rfl | hj
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hj)
  · have q2 : lz σ / 2 / 32 < 2 ^ KWH P := by
      have := lzb σ e; have := kwh_ge (P := P); have : P.W = 2 * P.w + 2 := rfl; omega
    have et : lz σ / 2 % 32 + 32 * (lz σ / 2 / 32 % 2 ^ KWH P) = lz σ / 2 := by rw [Nat.mod_eq_of_lt q2]; omega
    by_cases c1 : j = wG
    · subst c1; simp only [WSV, rootW]; rd_up; rw [et, vZ σ e, z0 σ e]
    · by_cases c2 : j = wS
      · subst c2; simp only [rootW]; rd_up; rw [et]
      · have c3 : j ≠ wF := (hLWT j (by rcases List.mem_cons.mp hj with h | h; exact absurd h c1; exact h)).2.1
        simp only [upd_ne _ _ c1, upd_ne _ _ c2, upd_ne _ _ c3]
  · simp only [List.mem_cons] at hd ⊢
    rcases hd with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  · have hd' : d = sOk5 ∨ d ∈ LS := List.mem_cons.mp hd
    simp only [WSV]
    rcases hd' with rfl | hd'
    · rd_up
    · simp only [upd_ne _ _ (hLS d hd').2.2.2.1, upd_ne _ _ (hLS d hd').2.2.1, upd_ne _ _ (hLS d hd').2.1]

end

end VG.Proof.Rsa.Arm.RecoverDet
