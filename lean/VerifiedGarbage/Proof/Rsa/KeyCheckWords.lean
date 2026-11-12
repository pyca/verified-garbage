module

public import VerifiedGarbage.Proof.Rsa.KeyCheckMath
import VerifiedGarbage.Proof.Framework.Omega

/-!
# RSA: the key checks of a balanced key, by words

For a key whose `p` and `q` have `w / 2` words of `n`'s `w` (of 32 bits): `p q = n` is
`p q mod 2^(32 w) = n`, exact there; and the remainders modulo `p`, `p - 1` and `q - 1` may be
taken modulo the divisors with their top words made not zero (`fixT`), which `p q = n` already
makes them, as `n` has `w` words. `keyBits_words`: these checks are `keyBits'` of the
quotient and remainder of `n / p` and the remainders themselves.
-/

@[expose] public section

namespace VG.Proof.Rsa

open VG.Spec.Rsa

/-- A number `x` of `k` words with `2^(32 (k - 1))` added if its top word is zero. -/
def fixT (k x : Nat) : Nat := if x / 2 ^ (32 * (k - 1)) = 0 then x + 2 ^ (32 * (k - 1)) else x

theorem fixT_lt {k x : Nat} (hk : 1 ≤ k) (hx : x < 2 ^ (32 * k)) : fixT k x < 2 ^ (32 * k) := by
  have e : (2 : Nat) ^ (32 * k) = 2 ^ (32 * (k - 1)) * 2 ^ 32 := by rw [← Nat.pow_add]; congr 1; omega
  have hP := Nat.two_pow_pos (32 * (k - 1))
  unfold fixT
  split
  · rename_i h0
    have : x < 2 ^ (32 * (k - 1)) := by
      rcases Nat.lt_or_ge x (2 ^ (32 * (k - 1))) with h | h
      · exact h
      · exact absurd h0 (Nat.pos_iff_ne_zero.mp (Nat.div_pos h hP))
    rw [e]
    have : 2 ^ (32 * (k - 1)) * 2 ≤ 2 ^ (32 * (k - 1)) * 2 ^ 32 := Nat.mul_le_mul_left _ (by decide)
    omega
  · exact hx

theorem fixT_ge {k x : Nat} : 2 ^ (32 * (k - 1)) ≤ fixT k x := by
  unfold fixT
  split
  · omega
  · rename_i h0
    exact Nat.le_of_not_lt fun h => h0 (Nat.div_eq_of_lt h)

theorem fixT_of_ge {k x : Nat} (h : 2 ^ (32 * (k - 1)) ≤ x) : fixT k x = x := by
  unfold fixT
  have : x / 2 ^ (32 * (k - 1)) ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.div_pos h (Nat.two_pow_pos _))
  simp only [this, ↓reduceIte]

/-- A product below the square of a bound. -/
theorem mul_lt_sq {a b P : Nat} (ha : a < P) (hb : b < P) : a * b < P * P :=
  Nat.lt_of_le_of_lt (Nat.mul_le_mul_left a (Nat.le_of_lt hb)) (Nat.mul_lt_mul_of_pos_right ha (by omega))

/-- For a valid modulus `n = p q` of `w` words (`w` even), with `p` and `q` of `w / 2`
words: both have their top words, and so do `p - 1` and `q - 1`. -/
theorem top_words {k n p q w : Nat} (hm : modulusValid n k = true) (hw : w = (k + 3) / 4) (hw4 : 4 ≤ w)
    (hp : p < 2 ^ (32 * (w / 2))) (hq : q < 2 ^ (32 * (w / 2))) (hN : p * q = n) :
    2 ^ (32 * (w / 2 - 1)) ≤ p ∧ 2 ^ (32 * (w / 2 - 1)) ≤ 2 * (p / 2) ∧
      2 ^ (32 * (w / 2 - 1)) ≤ 2 * (q / 2) := by
  obtain ⟨hn, hnk⟩ := modulusValid_facts hm
  have lo : 2 ^ (32 * (w / 2 - 1)) * 2 ^ (32 * (w / 2)) ≤ n := by
    rw [← Nat.pow_add]
    have h8 : (2 : Nat) ^ (8 * (k - 1)) ≤ n := by
      rw [Nat.pow_mul, show (2 : Nat) ^ 8 = 256 from rfl]; exact hnk
    exact Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega)) h8
  have pT : 2 ^ (32 * (w / 2 - 1)) ≤ p := Nat.le_of_not_lt fun h => by
    have := Nat.lt_of_le_of_lt (Nat.mul_le_mul_left p (Nat.le_of_lt hq))
      (Nat.mul_lt_mul_of_pos_right h (Nat.two_pow_pos (32 * (w / 2))))
    omega
  have qT : 2 ^ (32 * (w / 2 - 1)) ≤ q := Nat.le_of_not_lt fun h => by
    have := Nat.lt_of_le_of_lt (Nat.mul_le_mul_left q (Nat.le_of_lt hp))
      (Nat.mul_lt_mul_of_pos_right h (Nat.two_pow_pos (32 * (w / 2))))
    rw [Nat.mul_comm q] at this
    omega
  have ev : 2 ^ (32 * (w / 2 - 1)) % 2 = 0 := by
    rw [show 32 * (w / 2 - 1) = 32 * (w / 2 - 1) - 1 + 1 by omega, Nat.pow_succ, Nat.mul_mod_left]
  exact ⟨pT, by omega, by omega⟩

/-- The checks a balanced key's code computes, in its order. -/
def keyBitsW (w n d p q dP dQ qInv R₁ R₂ : Nat) : Bool :=
  decide (p % 2 = 1) && decide (p * q % 2 ^ (32 * w) = n) && decide (dP < 2 * (p / 2)) &&
    decide (R₁ = 1) && decide (dQ < 2 * (q / 2)) && decide (R₂ = 1) && decide (qInv < p) &&
    decide (q * qInv % 2 ^ (32 * w) % fixT (w / 2) p = 1) && decide (d < n) &&
    decide (d % fixT (w / 2) (2 * (p / 2)) = dP) && decide (d % fixT (w / 2) (2 * (q / 2)) = dQ)

/-- A balanced key's checks are `keyBits'` of the division of `n` by `p` and of the remainders. -/
theorem keyBits_words {k n d p q dP dQ qInv w R₁ R₂ : Nat} (hm : modulusValid n k = true)
    (hw : w = (k + 3) / 4) (hw4 : 4 ≤ w) (he : w % 2 = 0) (hp : p < 2 ^ (32 * (w / 2)))
    (hq : q < 2 ^ (32 * (w / 2))) :
    keyBitsW w n d p q dP dQ qInv R₁ R₂ =
      keyBits' n d p q dP dQ qInv (n / p) (n % p) R₁ R₂ (q % 2 ^ (32 * w) * qInv % p) (d % (2 * (p / 2)))
        (d % (2 * (q / 2))) := by
  obtain ⟨hn, hnk⟩ := modulusValid_facts hm
  have hW : (2 : Nat) ^ (32 * w) = 2 ^ (32 * (w / 2)) * 2 ^ (32 * (w / 2)) := by
    rw [← Nat.pow_add]; congr 1; omega
  have hpq : p * q < 2 ^ (32 * w) := by rw [hW]; exact mul_lt_sq hp hq
  have hq' : q < 2 ^ (32 * w) := Nat.lt_of_lt_of_le hq (Nat.pow_le_pow_right (by decide) (by omega))
  unfold keyBitsW keyBits' crtBits
  rw [Nat.mod_eq_of_lt hpq, Nat.mod_eq_of_lt hq']
  by_cases hP : p % 2 = 1
  · by_cases hN : p * q = n
    · -- `p q = n`: `p` and `q` have their top words.
      have hP0 : 0 < p := by omega
      obtain ⟨pT, pT', qT'⟩ := top_words hm hw hw4 hp hq hN
      have hdiv : n / p = q := Nat.div_eq_of_eq_mul_left hP0 (by rw [← hN, Nat.mul_comm])
      have hmod : n % p = 0 := by rw [← hN]; exact Nat.mul_mod_right p q
      rw [fixT_of_ge pT, fixT_of_ge pT', fixT_of_ge qT', hdiv, hmod]
      simp only [hP, hN, decide_true, Bool.true_and]
      by_cases hi : qInv < p
      · rw [Nat.mod_eq_of_lt (show q * qInv < 2 ^ (32 * w) by rw [hW]; exact mul_lt_sq hq (Nat.lt_trans hi hp))]
      · simp [hi]
    · have : ¬(n / p = q ∧ n % p = 0) := fun ⟨a, b⟩ => hN (mul_of_div a b)
      simp only [hP, hN, decide_true, decide_false, Bool.true_and, Bool.false_and, Bool.and_false]
      by_cases a : n / p = q
      · simp [a, show ¬n % p = 0 from fun b => this ⟨a, b⟩]
      · simp [a]
  · simp [hP]

/-- With the products `e dP` and `e dQ` by words too: `dX e mod 2^(32 w)` (exact for `e < 2^33`)
modulo the divisor with its top word made not zero. -/
theorem keyBits_words2 {k n e d p q dP dQ qInv w : Nat} (hm : modulusValid n k = true)
    (hw : w = (k + 3) / 4) (hw4 : 4 ≤ w) (he2 : w % 2 = 0) (hp : p < 2 ^ (32 * (w / 2)))
    (hq : q < 2 ^ (32 * (w / 2))) (hdp : dP < 2 ^ (32 * (w / 2))) (hdq : dQ < 2 ^ (32 * (w / 2)))
    (he : e < 2 ^ 33) :
    keyBitsW w n d p q dP dQ qInv (dP * e % 2 ^ (32 * w) % fixT (w / 2) (2 * (p / 2)))
        (dQ * e % 2 ^ (32 * w) % fixT (w / 2) (2 * (q / 2))) =
      keyBits' n d p q dP dQ qInv (n / p) (n % p) (e % 2 ^ 33 * dP % (2 * (p / 2)))
        (e % 2 ^ 33 * dQ % (2 * (q / 2))) (q % 2 ^ (32 * w) * qInv % p) (d % (2 * (p / 2)))
        (d % (2 * (q / 2))) := by
  rw [← keyBits_words hm hw hw4 he2 hp hq]
  have hW : (2 : Nat) ^ (32 * w) = 2 ^ (32 * (w / 2)) * 2 ^ (32 * (w / 2)) := by
    rw [← Nat.pow_add]; congr 1; omega
  by_cases hN : p * q = n
  · obtain ⟨-, pT', qT'⟩ := top_words hm hw hw4 hp hq hN
    have eB : e < 2 ^ (32 * (w / 2)) := Nat.lt_of_lt_of_le he (Nat.pow_le_pow_right (by decide) (by omega))
    rw [fixT_of_ge pT', fixT_of_ge qT', Nat.mod_eq_of_lt (show dP * e < 2 ^ (32 * w) by rw [hW]; exact mul_lt_sq hdp eB),
      Nat.mod_eq_of_lt (show dQ * e < 2 ^ (32 * w) by rw [hW]; exact mul_lt_sq hdq eB), Nat.mod_eq_of_lt he,
      Nat.mul_comm dP e, Nat.mul_comm dQ e]
  · have hpq : p * q % 2 ^ (32 * w) ≠ n := by
      rw [Nat.mod_eq_of_lt (show p * q < 2 ^ (32 * w) by rw [hW]; exact mul_lt_sq hp hq)]; exact hN
    simp [keyBitsW, hpq]

end VG.Proof.Rsa
