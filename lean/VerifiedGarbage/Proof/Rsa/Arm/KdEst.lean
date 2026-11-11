module

public import VerifiedGarbage.Proof.Rsa.Arm.KdRefine
import VerifiedGarbage.Proof.Bignum.WordTop32
import VerifiedGarbage.Proof.Bignum.WordStepNorm32
import VerifiedGarbage.Proof.Bignum.WordStep32
import VerifiedGarbage.Proof.Rsa.Arm.KdTop

/-! # A step's estimate of the key checks' division on ARMv7 (`KeyDiv.estimate`) -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.KeyDiv

open VG VG.Arm VG.Impl.Rsa.Arm.KeyDiv VG.Proof.Rsa.Arm.Keys VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

open VG.Proof.Bignum.WordStep32 VG.Proof.Bignum.WordTop32 in
/-- The estimate's arithmetic: for a window `Y < 2^32 M` whose top four words
are `a₁ a₂ a₃ a` (`k` words `L` below), `u₂ u₁ u₀` the top three words of
`Y 2^z` and `D = Dh 2^32 + Dl` the top two of `M 2^z`, `M 2^z < 2^(32 (k + 3))`
normalized: `u₂ ≤ Dh`, `U < (2^32 + 1) D`, the 2-by-1 estimate within 2 above
`Q = min(⌊U / D⌋, 2^32 - 1)`, and `⌊Y / M⌋ ≤ Q ≤ ⌊Y / M⌋ + 1`. -/
theorem est_math {Y M z k L a a1 a2 a3 Dh Dl u2 u1 u0 : Nat} (hz : z ≤ 31)
    (hY : Y = L + 2 ^ (32 * k) * a + 2 ^ (32 * k) * 2 ^ 32 * (a3 + 2 ^ 32 * a2 + 2 ^ 64 * a1))
    (hL : L < 2 ^ (32 * k)) (ha : a < 2 ^ 32) (ha2 : a2 < 2 ^ 32) (ha3 : a3 < 2 ^ 32)
    (hYM : Y < M * 2 ^ 32) (hMP : M * 2 ^ z < 2 ^ (32 * (k + 3)))
    (hD : Dh * 2 ^ 32 + Dl = M * 2 ^ z / 2 ^ (32 * (k + 1))) (hDn : 2 ^ 31 ≤ Dh) (hDl : Dl < 2 ^ 32)
    (hu2 : u2 = wordP a1 a2 (2 ^ z)) (hu1 : u1 = wordP a2 a3 (2 ^ z)) (hu0 : u0 = wordP a3 a (2 ^ z)) :
    u2 ≤ Dh ∧ u2 * 2 ^ 64 + u1 * 2 ^ 32 + u0 < (2 ^ 32 + 1) * (Dh * 2 ^ 32 + Dl) ∧
    min ((u2 * 2 ^ 64 + u1 * 2 ^ 32 + u0) / (Dh * 2 ^ 32 + Dl)) (2 ^ 32 - 1) ≤
      min ((u2 * 2 ^ 32 + u1) / Dh) (2 ^ 32 - 1) ∧
    min ((u2 * 2 ^ 32 + u1) / Dh) (2 ^ 32 - 1) ≤
      min ((u2 * 2 ^ 64 + u1 * 2 ^ 32 + u0) / (Dh * 2 ^ 32 + Dl)) (2 ^ 32 - 1) + 2 ∧
    Y / M ≤ min ((u2 * 2 ^ 64 + u1 * 2 ^ 32 + u0) / (Dh * 2 ^ 32 + Dl)) (2 ^ 32 - 1) ∧
    min ((u2 * 2 ^ 64 + u1 * 2 ^ 32 + u0) / (Dh * 2 ^ 32 + Dl)) (2 ^ 32 - 1) ≤ Y / M + 1 := by
  have hP := Nat.two_pow_pos z
  have eK : (2 : Nat) ^ (32 * (k + 1)) = 2 ^ (32 * k) * 2 ^ 32 := by
    rw [show 32 * (k + 1) = 32 * k + 32 by omega, Nat.pow_add]
  have hL' : L + 2 ^ (32 * k) * a < 2 ^ (32 * (k + 1)) := by
    rw [eK]
    have := Nat.mul_le_mul_left (2 ^ (32 * k)) (show a + 1 ≤ 2 ^ 32 by omega)
    rw [Nat.mul_add, Nat.mul_one] at this; omega
  -- `Y 2^z < 2^32 M 2^z < 2^(32 (k + 4))`.
  have hYP : Y * 2 ^ z < M * 2 ^ z * 2 ^ 32 := by
    rw [Nat.mul_right_comm]; exact Nat.mul_lt_mul_of_pos_right hYM hP
  have hY' : Y = (L + 2 ^ (32 * k) * a) + 2 ^ (32 * (k + 1)) * a3 +
      2 ^ (32 * (k + 1)) * 2 ^ 32 * (a2 + 2 ^ 32 * a1) := by
    rw [hY, eK]; grind
  have hsm : a1 * 2 ^ z < 2 ^ 32 := by
    refine top_small (L := L + 2 ^ (32 * k) * a) (k := k + 1) (a2 := a2) (a3 := a3) ?_
    rw [← hY', show 32 * (k + 1 + 3) = 32 * (k + 3) + 32 by omega, Nat.pow_add]
    exact Nat.lt_of_lt_of_le hYP (Nat.mul_le_mul_right _ (Nat.le_of_lt hMP))
  have e2 : u2 = a1 * 2 ^ z % 2 ^ 32 + a2 * 2 ^ z / 2 ^ 32 := by
    rw [hu2]; exact Nat.mod_eq_of_lt (lohi_lt (by omega) ha2)
  have e1 : u1 = a2 * 2 ^ z % 2 ^ 32 + a3 * 2 ^ z / 2 ^ 32 := by
    rw [hu1]; exact Nat.mod_eq_of_lt (lohi_lt (by omega) ha3)
  have e0 : u0 = a3 * 2 ^ z % 2 ^ 32 + a * 2 ^ z / 2 ^ 32 := by
    rw [hu0]; exact Nat.mod_eq_of_lt (lohi_lt (by omega) ha)
  have hU : u2 * 2 ^ 64 + u1 * 2 ^ 32 + u0 = Y * 2 ^ z / 2 ^ (32 * k + 32) := by
    rw [e2, e1, e0, top3_math hz hL hsm, ← hY]
    exact congrArg (Y * 2 ^ z / ·) (Nat.pow_add 2 (32 * k) 32).symm
  have hu0' : u0 < 2 ^ 32 := hu0 ▸ Nat.mod_lt _ (by decide)
  have hu1' : u1 < 2 ^ 32 := hu1 ▸ Nat.mod_lt _ (by decide)
  have hDD : M * 2 ^ z / 2 ^ (32 * k + 32) = Dh * 2 ^ 32 + Dl := by
    rw [hD, show 32 * (k + 1) = 32 * k + 32 by omega]
  have hDh : (Dh * 2 ^ 32 + Dl) / 2 ^ 32 = Dh := by omega_using [hDl]
  have hUh : (u2 * 2 ^ 64 + u1 * 2 ^ 32 + u0) / 2 ^ 32 = u2 * 2 ^ 32 + u1 := by omega_using [hu0']
  have q := qhat3_div (Y := Y) (M := M) (P := 2 ^ z) (K := 32 * k) hP hYM (by rw [hDD, hDh]; exact hDn)
  rw [hDD, ← hU, hDh, hUh] at q
  refine ⟨?_, q⟩
  -- `u₂ = ⌊Y 2^z / 2^(32 (k + 3))⌋ ≤ ⌊2^32 M 2^z / 2^(32 (k + 3))⌋ = Dh`.
  have h2 : u2 = (u2 * 2 ^ 64 + u1 * 2 ^ 32 + u0) / 2 ^ 64 := by omega_using [hu0', hu1']
  have hd2 : Dh = M * 2 ^ z * 2 ^ 32 / 2 ^ (32 * k + 32) / 2 ^ 64 := by
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, show 32 * k + 32 + 64 = (32 * k + 64) + 32 by omega,
      Nat.pow_add 2 (32 * k + 64) 32, Nat.mul_div_mul_right _ _ (Nat.two_pow_pos 32),
      show 32 * k + 64 = (32 * k + 32) + 32 by omega, Nat.pow_add 2 (32 * k + 32) 32, ← Nat.div_div_eq_div_mul,
      hDD, hDh]
  rw [h2, hU, hd2]
  exact Nat.div_le_div_right (Nat.div_le_div_right (Nat.le_of_lt hYP))

end VG.Proof.Rsa.Arm.KeyDiv
