module

public import VerifiedGarbage.Proof.Rsa.RecoverDetModel
import VerifiedGarbage.Proof.Framework.Omega

-- separate module: target-independent, shared verbatim by every architecture's stage after the square root

/-!
# Appendix C.2's model: the root as `isqrt`

`root_bridge`: where the model's earlier checks pass (`m < n`, `q` the quotient
of `n - r` by `m + 1`, and `b² > 4 n`, so that `b ≤ n + 1`), the model's
bit-serial root of `X = b² - 4 n` (`rootOf`, by `sqrtStep`) is `isqrt X`, its
remainder is zero exactly where `X` is a square, and `isqrt X < 2^nb`. A square
root by words, which computes `isqrt X` and whether `X` is a square, is the
model's there.
-/

@[expose] public section

namespace VG.Proof.Rsa.RecoverDet

open VG.Spec.Rsa (isqrt)

/-- Where `m < n`, `q` is the quotient of `n - r` by `m + 1` and `b² > 4 n`, so that `b ≤ n + 1`: the
model's root (`rootOf`) is `isqrt X` of `X = b² - 4 n` (`xOf`), its remainder zero exactly where `X` is a
square, and `isqrt X < 2^nb`. -/
theorem root_bridge {nb wb n de q : Nat} (three : 3 ≤ n) (hn : 8 * (n + 2) ≤ 2 ^ nb) (hw : 2 * nb ≤ wb)
    (hwe : wb % 2 = 0) (hlt : ltOf nb wb n de = true) (hq : q = dOf nb wb n de / m1Of nb wb n de)
    (h4 : ok4Of nb wb n (bOf nb q) = true) :
    (rootOf nb wb n (bOf nb q)).2.2 = isqrt (xOf nb wb n (bOf nb q)) ∧
      ((rootOf nb wb n (bOf nb q)).2.1 = 0 ↔
        isqrt (xOf nb wb n (bOf nb q)) * isqrt (xOf nb wb n (bOf nb q)) = xOf nb wb n (bOf nb q)) ∧
      isqrt (xOf nb wb n (bOf nb q)) < 2 ^ nb := by
  have pnb : 2 ^ nb ≤ 2 ^ wb := Nat.pow_le_pow_right (by decide) (by omega)
  have p2 : 2 ^ nb * 2 ^ nb ≤ 2 ^ wb := by rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)
  have rlt : rOf nb wb n de < n := Nat.mod_lt _ (by omega)
  have dv : dOf nb wb n de = n - rOf nb wb n de := by
    unfold dOf; rw [Nat.mod_eq_of_lt (by omega), wsub_of_le (by omega) (by omega)]
  have mlt : mOf nb wb n de < n := by simpa [ltOf] using hlt
  have m1 : m1Of nb wb n de = mOf nb wb n de + 1 := by
    unfold m1Of; rw [Nat.mod_eq_of_lt (a := mOf nb wb n de) (by omega), Nat.mod_eq_of_lt (by omega)]
  have qle : q ≤ n := by rw [hq, dv, m1]; exact Nat.le_trans (Nat.div_le_self _ _) (by omega)
  have hb : bOf nb q = q + 1 := by unfold bOf; exact Nat.mod_eq_of_lt (by omega)
  rw [hb] at h4 ⊢
  have hb1 : q + 1 ≤ n + 1 := by omega
  generalize q + 1 = b at *
  have blt : b < 2 ^ nb := by omega
  have bb : b * b < 2 ^ wb := Nat.lt_of_lt_of_le (Nat.mul_lt_mul'' blt blt) p2
  have sq : sqOf nb wb b = b * b := by
    unfold sqOf; rw [prod_iter _ _ _ (by omega)]; simp only
    rw [Nat.mod_eq_of_lt blt, Nat.mod_eq_of_lt bb]
  have f4 : fourN wb n = 4 * n := by
    unfold fourN
    rw [Nat.mod_eq_of_lt (a := 2 * n) (by omega), Nat.mod_eq_of_lt (by omega)]; grind
  have big : ¬ (b * b < 4 * n) ∧ ¬ (xOf nb wb n b < 1) := by
    unfold ok4Of at h4; rw [sq, f4] at h4; simpa using h4
  have xv : xOf nb wb n b = b * b - 4 * n := by
    unfold xOf; rw [sq, f4, wsub_of_le bb (by omega)]
  rw [xv]
  have rootLt : isqrt (b * b - 4 * n) < b := by
    refine Nat.lt_of_not_le fun c => ?_
    have := isqrt_sq_le (b * b - 4 * n)
    have : b * b ≤ isqrt (b * b - 4 * n) * isqrt (b * b - 4 * n) := Nat.mul_self_le_mul_self c
    omega
  have K : 4 ^ (wb / 2) = 2 ^ wb := by
    rw [show (4 : Nat) = 2 ^ 2 by rfl, ← Nat.pow_mul]; congr 1; omega
  obtain ⟨ry, rr⟩ := sqrt_iter (nb := nb) (K := wb / 2) (X := b * b - 4 * n) (by rw [K]; omega)
    (by have := Nat.div_mul_le_self (2 ^ nb) 8; have : n + 1 < 2 ^ nb / 8 := by omega
        omega)
  have wbK : 2 * (wb / 2) = wb := by omega
  rw [wbK] at ry rr
  unfold rootOf
  rw [xv, ry]
  exact ⟨rfl, by omega, by omega⟩

end VG.Proof.Rsa.RecoverDet
