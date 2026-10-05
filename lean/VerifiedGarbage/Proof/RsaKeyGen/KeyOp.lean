import VerifiedGarbage.Proof.RsaKeyGen.KeyCheck

/-!
# An RSA key from its primes: `keyFromPrimes` as `vg_rsa_keygen_key` computes it

With `p ≥ q` (swapped), `L = lcm(p − 1, q − 1)` and `d = e⁻¹ mod L`, and
`x` the inverse of `q` modulo `M = qMod p` (`p` if it is odd and at least
3, else 3) that `inverse` finds, `keyFromPrimes` is `.inr ()` for
`d ≤ 2^(8 pLen)`, and otherwise the key exactly when the code's mask holds:
`n`'s top bit, `gcd(q, M) = 1`, `p` and `q` odd and `e` valid
(`keyFromPrimes_code`).
-/

namespace VG.Proof.RsaKeyGen

open VG.Spec.RsaKeyGen
open VG.Proof.Rsa (inverse_eq inverse_none)

/-- The modulus of `qInv`: `p` if it is odd and at least 3, else 3. -/
def qModP (P : Nat) : Nat := if (decide (P % 2 = 1) && !decide (P < 3)) = true then P else 3

/-- `d > 2` exists modulo `L = lcm(p − 1, q − 1)` only for `p ≥ 3`, `q ≥ 2`,
and then `d < L`. -/
theorem primes_of_inverse {e P Q d : Nat} (hqp : Q ≤ P)
    (hd : Spec.Rsa.inverse e (Nat.lcm (P - 1) (Q - 1)) = some d) (hd2 : 2 ≤ d) :
    3 ≤ P ∧ 2 ≤ Q ∧ d < Nat.lcm (P - 1) (Q - 1) := by
  obtain ⟨hed, hdL⟩ := inverse_some hd
  generalize hL : Nat.lcm (P - 1) (Q - 1) = L at hed hdL ⊢
  have hL0 : 0 < L := by
    rcases Nat.eq_zero_or_pos L with h | h
    · subst h
      rw [Nat.mod_zero] at hed
      have : d ≤ 1 := by
        rcases Nat.eq_zero_or_pos e with h0 | h0
        · subst h0; omega
        · exact Nat.le_of_dvd (by decide) ⟨e, by rw [← hed, Nat.mul_comm]⟩
      omega
    · exact h
  have hdL := hdL hL0
  have hq1 : Q - 1 ≠ 0 := fun h => by rw [h, Nat.lcm_zero_right] at hL; omega
  have hLle : L ≤ (P - 1) * (Q - 1) := by
    rw [← hL]
    exact Nat.le_of_dvd (Nat.mul_pos (by omega) (by omega)) (Nat.lcm_dvd_mul _ _)
  have hp3 : 3 ≤ P := by
    by_contra h
    have : (P - 1) * (Q - 1) ≤ 1 := by
      have : P - 1 ≤ 1 := by omega
      have : Q - 1 ≤ 1 := by omega
      exact Nat.mul_le_mul (by omega) (by omega) |>.trans (by decide)
    omega
  exact ⟨hp3, by omega, hdL⟩

/-- The key from the primes, as the code computes it. -/
theorem keyFromPrimes_code {pLen e P₀ Q₀ x : Nat} (hl1 : 32 ≤ pLen) (hl2 : pLen ≤ 512)
    (hP₀ : P₀ < 2 ^ (8 * pLen)) (hQ₀ : Q₀ < 2 ^ (8 * pLen)) (he : e < 2 ^ 64)
    (hx : ((qModP (if P₀ < Q₀ then Q₀ else P₀) : Nat) : Int) ∣
      (x : Int) * (if P₀ < Q₀ then P₀ else Q₀) -
        Nat.gcd (if P₀ < Q₀ then P₀ else Q₀) (qModP (if P₀ < Q₀ then Q₀ else P₀)))
    (hxl : x < qModP (if P₀ < Q₀ then Q₀ else P₀)) :
    let P := if P₀ < Q₀ then Q₀ else P₀
    let Q := if P₀ < Q₀ then P₀ else Q₀
    keyFromPrimes (16 * pLen) e P₀ Q₀ =
      match Spec.Rsa.inverse e (Nat.lcm (P - 1) (Q - 1)) with
      | none => .inl (.error .internal)
      | some d =>
        if d ≤ 2 ^ (8 * pLen) then .inr ()
        else if (decide (2 ^ (16 * pLen - 1) ≤ P * Q) && decide (Nat.gcd Q (qModP P) = 1) &&
            decide (P % 2 = 1) && decide (Q % 2 = 1) && Spec.Rsa.exponentValid e) = true then
          .inl (.ok ⟨P * Q, e, d, P, Q, d % (P - 1), d % (Q - 1), x⟩)
        else .inl (.error .internal) := by
  intro P Q
  have hswap : (if P₀ < Q₀ then (Q₀, P₀) else (P₀, Q₀)) = (P, Q) := by
    by_cases h : P₀ < Q₀ <;> simp [P, Q, h]
  have hqp : Q ≤ P := by by_cases h : P₀ < Q₀ <;> simp [P, Q, h] <;> omega
  have hP : P < 2 ^ (8 * pLen) := by by_cases h : P₀ < Q₀ <;> simp [P, h] <;> omega
  unfold keyFromPrimes
  rw [hswap]
  dsimp only
  rcases hd : Spec.Rsa.inverse e (Nat.lcm (P - 1) (Q - 1)) with _ | d
  · rfl
  · dsimp only
    rw [show 16 * pLen / 2 = 8 * pLen by omega]
    by_cases hsm : d ≤ 2 ^ (8 * pLen)
    · rw [ite_eq_left hsm, ite_eq_left hsm]
    · rw [ite_eq_right hsm, ite_eq_right hsm]
      have h2 : 2 ≤ 2 ^ (8 * pLen) := Nat.le_self_pow (by omega) 2 |>.trans' (by decide)
      obtain ⟨hp3, hq2, hdL⟩ := primes_of_inverse hqp hd (by omega)
      have hdb : 2 ^ (8 * pLen) < d := by omega
      by_cases hc : (decide (2 ^ (16 * pLen - 1) ≤ P * Q) && decide (Nat.gcd Q (qModP P) = 1) &&
          decide (P % 2 = 1) && decide (Q % 2 = 1) && Spec.Rsa.exponentValid e) = true
      · rw [ite_eq_left hc]
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        obtain ⟨⟨⟨⟨htop, hg⟩, hpo⟩, hqo⟩, hev⟩ := hc
        have hM : qModP P = P := by unfold qModP; simp [hpo]; omega
        rw [hM] at hg hx hxl
        have hqi : Spec.Rsa.inverse Q P = some x := inverse_eq (by omega) hxl (by rw [hg] at hx; exact_mod_cast hx)
        rw [hqi]
        dsimp only
        rw [ite_eq_left ((keyCheck_iff hl1 hl2 hP hqp he hd hdb hqi).mpr ⟨hpo, hqo, htop, hev⟩)]
      · rw [ite_eq_right hc]
        rcases hqi : Spec.Rsa.inverse Q P with _ | qInv
        · rfl
        · dsimp only
          refine ite_eq_right fun hk => ?_
          obtain ⟨hpo, hqo, htop, hev⟩ := (keyCheck_iff hl1 hl2 hP hqp he hd hdb hqi).mp hk
          have hM : qModP P = P := by unfold qModP; simp [hpo]; omega
          apply hc
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          refine ⟨⟨⟨⟨htop, ?_⟩, hpo⟩, hqo⟩, hev⟩
          rw [hM]
          by_contra hg
          rw [inverse_none hg] at hqi
          cases hqi

end VG.Proof.RsaKeyGen
