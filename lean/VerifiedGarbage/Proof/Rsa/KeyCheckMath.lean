module

public import VerifiedGarbage.Proof.Rsa.KeyParts
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# RSA: the key checks from a division and products modulo `p - 1`

For an implementation that checks `p q = n` as `p` odd, `n / p = q` and
`n mod p = 0`, takes `p - 1` and `q - 1` as `p` and `q` with their low bits
cleared, and the congruences as products compared with 1 (each known only
when its factor is below its modulus): `crtKeyValid_bits`. `keyValid_bits`:
then `d e ≡ 1 (mod p - 1)` is `d mod (p - 1) = dP`, as `dP` is the inverse
of `e` modulo `p - 1`.
-/

@[expose] public section

namespace VG.Proof.Rsa

open VG.Spec.Rsa

/-- The checks of `crtKeyValid` in the order the code computes them, from
the quotient `X₁` and remainder `X₂` of `n / p` and the products `R₁`,
`R₂`, `R₃` of `e dP`, `e dQ` and `q qInv` modulo `p - 1`, `q - 1`, `p`. -/
def crtBits (p q dP dQ qInv X₁ X₂ R₁ R₂ R₃ : Nat) : Bool :=
  decide (p % 2 = 1) && decide (X₁ = q) && decide (X₂ = 0) && decide (dP < 2 * (p / 2)) &&
    decide (R₁ = 1) && decide (dQ < 2 * (q / 2)) && decide (R₂ = 1) && decide (qInv < p) &&
    decide (R₃ = 1)

/-- Then those of `d`: `d < n`, and its remainders `Y₁`, `Y₂` modulo `p - 1`
and `q - 1` are `dP` and `dQ`. -/
def keyBits' (n d p q dP dQ qInv X₁ X₂ R₁ R₂ R₃ Y₁ Y₂ : Nat) : Bool :=
  crtBits p q dP dQ qInv X₁ X₂ R₁ R₂ R₃ && decide (d < n) && decide (Y₁ = dP) && decide (Y₂ = dQ)

theorem odd_factor {P Q N : Nat} (h : P * Q = N) (hN : N % 2 = 1) : P % 2 = 1 := by
  rcases Nat.mod_two_eq_zero_or_one P with hP | hP
  · rw [← h, Nat.mul_mod, hP, Nat.zero_mul] at hN; exact absurd hN (by decide)
  · exact hP

theorem mul_of_div {N P Q : Nat} (hq : N / P = Q) (hr : N % P = 0) : P * Q = N := by
  have := Nat.div_add_mod N P
  rw [hq, hr, Nat.add_zero] at this
  exact this

/-- What a valid modulus gives. -/
theorem modulusValid_facts {n k : Nat} (hm : modulusValid n k = true) : n % 2 = 1 ∧ 256 ^ (k - 1) ≤ n := by
  simp only [modulusValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hm
  exact ⟨hm.1.1.1, hm.2⟩

theorem crtKeyValid_bits {k n e p q dP dQ qInv : Nat} (hm : modulusValid n k = true)
    (he : exponentValid e = true) (hp : p < 256 ^ (k - 1)) (hq : q < 256 ^ (k - 1))
    {X₁ X₂ R₁ R₂ R₃ : Nat} (hX : 0 < p → X₁ = n / p ∧ X₂ = n % p)
    (hR₁ : dP < 2 * (p / 2) → R₁ = e * dP % (2 * (p / 2)))
    (hR₂ : dQ < 2 * (q / 2) → R₂ = e * dQ % (2 * (q / 2)))
    (hR₃ : qInv < p → R₃ = q * qInv % p) :
    crtKeyValid k n e p q dP dQ qInv = crtBits p q dP dQ qInv X₁ X₂ R₁ R₂ R₃ := by
  obtain ⟨hodd, hn⟩ := modulusValid_facts hm
  rw [Bool.eq_iff_iff]
  simp only [crtKeyValid, crtBits, hm, he, Bool.true_and, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    and_assoc]
  by_cases hpq : p * q = n
  · have p2 := factor_ge_two hpq hq hn
    have q2 := factor_ge_two (n := n) (q := p) (by rw [Nat.mul_comm]; exact hpq) hp hn
    have podd := odd_factor hpq hodd
    have qodd := odd_factor (by rw [Nat.mul_comm]; exact hpq) hodd
    obtain ⟨e1, e2⟩ := hX (by omega)
    have eq1 : X₁ = q := by rw [e1, ← hpq, Nat.mul_div_cancel_left _ (by omega)]
    have eq2 : X₂ = 0 := by rw [e2, ← hpq, Nat.mul_mod_right]
    have mp : 2 * (p / 2) = p - 1 := by omega
    have mq : 2 * (q / 2) = q - 1 := by omega
    rw [mp] at hR₁ ⊢
    rw [mq] at hR₂ ⊢
    constructor
    · rintro ⟨-, h1, h2, h3, h4, h5, h6⟩
      exact ⟨podd, eq1, eq2, h1, by rw [hR₁ h1]; exact h2, h3, by rw [hR₂ h3]; exact h4, h5,
        by rw [hR₃ h5]; exact h6⟩
    · rintro ⟨-, -, -, h1, h2, h3, h4, h5, h6⟩
      exact ⟨hpq, h1, by rw [← hR₁ h1]; exact h2, h3, by rw [← hR₂ h3]; exact h4, h5,
        by rw [← hR₃ h5]; exact h6⟩
  · constructor
    · rintro ⟨h, -⟩; exact absurd h hpq
    · rintro ⟨podd, h1, h2, -⟩
      obtain ⟨e1, e2⟩ := hX (by omega)
      exact absurd (mul_of_div (by rw [← e1, h1]) (by rw [← e2, h2])) hpq

/-- With `dP` the inverse of `e` modulo `M`, `d e ≡ 1 (mod M)` is `d mod M = dP`. -/
theorem inv_unique {M e d dP : Nat} (hdP : dP < M) (he : e * dP % M = 1) :
    d * e % M = 1 ↔ d % M = dP := by
  constructor
  · intro hde
    calc d % M = d * 1 % M := by rw [Nat.mul_one]
      _ = d * (e * dP % M) % M := by rw [he]
      _ = d * (e * dP) % M := Nat.mul_mod_mod _ _ _
      _ = d * e * dP % M := by rw [Nat.mul_assoc]
      _ = d * e % M * dP % M := (Nat.mod_mul_mod _ _ _).symm
      _ = dP % M := by rw [hde, Nat.one_mul]
      _ = dP := Nat.mod_eq_of_lt hdP
  · intro h
    rw [← Nat.mod_mul_mod, h, Nat.mul_comm, he]

theorem keyValid_crt {k n e d p q dP dQ qInv : Nat} (hm : modulusValid n k = true)
    (hp : p < 256 ^ (k - 1)) (hq : q < 256 ^ (k - 1)) :
    keyValid k n e d p q dP dQ qInv = (crtKeyValid k n e p q dP dQ qInv && decide (d < n) &&
      decide (d % (p - 1) = dP) && decide (d % (q - 1) = dQ)) := by
  have hn := (modulusValid_facts hm).2
  have hp' : p < n := Nat.lt_of_lt_of_le hp hn
  have hq' : q < n := Nat.lt_of_lt_of_le hq hn
  rw [Bool.eq_iff_iff]
  simp only [keyValid, crtKeyValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc]
  constructor
  · rintro ⟨hmv, hev, hdn, -, -, hpq, hd1, hd2, hP1, hP2, hQ1, hQ2, hI1, hI2⟩
    exact ⟨hmv, hev, hpq, hP1, hP2, hQ1, hQ2, hI1, hI2, hdn, (inv_unique hP1 hP2).1 hd1,
      (inv_unique hQ1 hQ2).1 hd2⟩
  · rintro ⟨hmv, hev, hpq, hP1, hP2, hQ1, hQ2, hI1, hI2, hdn, hY1, hY2⟩
    exact ⟨hmv, hev, hdn, hp', hq', hpq, (inv_unique hP1 hP2).2 hY1, (inv_unique hQ1 hQ2).2 hY2, hP1, hP2,
      hQ1, hQ2, hI1, hI2⟩

theorem keyValid_bits {k n e d p q dP dQ qInv : Nat} (hm : modulusValid n k = true)
    (he : exponentValid e = true) (hp : p < 256 ^ (k - 1)) (hq : q < 256 ^ (k - 1))
    {X₁ X₂ R₁ R₂ R₃ Y₁ Y₂ : Nat} (hX : 0 < p → X₁ = n / p ∧ X₂ = n % p)
    (hR₁ : dP < 2 * (p / 2) → R₁ = e * dP % (2 * (p / 2)))
    (hR₂ : dQ < 2 * (q / 2) → R₂ = e * dQ % (2 * (q / 2)))
    (hR₃ : qInv < p → R₃ = q * qInv % p)
    (hY₁ : 0 < 2 * (p / 2) → Y₁ = d % (2 * (p / 2))) (hY₂ : 0 < 2 * (q / 2) → Y₂ = d % (2 * (q / 2))) :
    keyValid k n e d p q dP dQ qInv = keyBits' n d p q dP dQ qInv X₁ X₂ R₁ R₂ R₃ Y₁ Y₂ := by
  rw [keyValid_crt hm hp hq, crtKeyValid_bits hm he hp hq hX hR₁ hR₂ hR₃, keyBits']
  by_cases hc : crtBits p q dP dQ qInv X₁ X₂ R₁ R₂ R₃ = true
  · have hv := hc
    rw [← crtKeyValid_bits hm he hp hq hX hR₁ hR₂ hR₃] at hv
    have hodd := (modulusValid_facts hm).1
    simp only [crtKeyValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] at hv
    obtain ⟨-, -, hpq, -⟩ := hv
    have hn := (modulusValid_facts hm).2
    have p2 := factor_ge_two hpq hq hn
    have q2 := factor_ge_two (n := n) (q := p) (by rw [Nat.mul_comm]; exact hpq) hp hn
    have podd := odd_factor hpq hodd
    have qodd := odd_factor (by rw [Nat.mul_comm]; exact hpq) hodd
    rw [hY₁ (by omega), hY₂ (by omega), show 2 * (p / 2) = p - 1 by omega, show 2 * (q / 2) = q - 1 by omega]
  · simp only [Bool.not_eq_true] at hc
    simp only [hc, Bool.false_and]

end VG.Proof.Rsa
