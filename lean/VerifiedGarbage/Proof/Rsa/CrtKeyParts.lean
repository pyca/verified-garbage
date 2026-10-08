import VerifiedGarbage.Proof.Rsa.KeyParts

/-!
# RSA: `crtKeyValid` from its parts

`crtKeyValid_parts`: for a valid modulus and exponent and `p` and `q`
shorter than the modulus, `crtKeyValid` is the conjunction of the checks an
implementation computes, with each remainder (`e dP mod (p - 1)`, …) known
only when the comparison before it holds and its prime is positive: when
`p q = n`, both primes are at least 2 (`factor_ge_two`).
-/

namespace VG.Proof.Rsa

open VG.Spec.Rsa

/-- The checks an implementation computes, from the remainders it computes
(`Rp = e dP mod Mp`, `Rq = e dQ mod Mq`, `Rpq = qInv q mod p`) and
`Mp = p - 1`, `Mq = q - 1`, in its order. -/
def crtKeyBits (n p q dP dQ qInv Mp Mq Rp Rq Rpq : Nat) : Bool :=
  true && decide (p * q = n) && decide (dP < Mp) && decide (Rp = 1) &&
    decide (dQ < Mq) && decide (Rq = 1) && decide (qInv < p) && decide (Rpq = 1)

theorem crtKeyValid_parts {k n e p q dP dQ qInv : Nat} (hm : modulusValid n k = true)
    (he : exponentValid e = true) (hp : p < 256 ^ (k - 1)) (hq : q < 256 ^ (k - 1)) {Mp Mq Rp Rq Rpq : Nat}
    (hMp : 0 < p → Mp = p - 1) (hMq : 0 < q → Mq = q - 1)
    (hRp : 0 < p → dP < Mp → Rp = e * dP % Mp) (hRq : 0 < q → dQ < Mq → Rq = e * dQ % Mq)
    (hRpq : 0 < p → qInv < p → Rpq = qInv * q % p) :
    crtKeyValid k n e p q dP dQ qInv = crtKeyBits n p q dP dQ qInv Mp Mq Rp Rq Rpq := by
  have hn : 256 ^ (k - 1) ≤ n := by
    simp only [modulusValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hm; exact hm.2
  rw [Bool.eq_iff_iff]
  simp only [crtKeyValid, crtKeyBits, hm, he, Bool.true_and, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    and_assoc]
  by_cases hpq : p * q = n
  · have hp2 := factor_ge_two hpq hq hn
    have hq2 := factor_ge_two (n := n) (q := p) (by rw [Nat.mul_comm]; exact hpq) hp hn
    rw [hMp (by omega), hMq (by omega)]
    rw [hMp (by omega)] at hRp
    rw [hMq (by omega)] at hRq
    constructor
    · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
      exact ⟨h1, h2, by rw [hRp (by omega) h2]; exact h3, h4, by rw [hRq (by omega) h4]; exact h5, h6,
        by rw [hRpq (by omega) h6, Nat.mul_comm]; exact h7⟩
    · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
      exact ⟨h1, h2, by rw [← hRp (by omega) h2]; exact h3, h4, by rw [← hRq (by omega) h4]; exact h5, h6,
        by rw [Nat.mul_comm, ← hRpq (by omega) h6]; exact h7⟩
  · constructor
    · rintro ⟨h, -⟩; exact absurd h hpq
    · rintro ⟨h, -⟩; exact absurd h hpq

end VG.Proof.Rsa
