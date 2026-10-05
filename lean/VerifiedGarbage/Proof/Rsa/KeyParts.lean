import VerifiedGarbage.Proof.Rsa.Octets

/-!
# RSA: `keyValid` from its parts

`keyValid_parts`: for a valid modulus and exponent and `p` and `q` shorter
than the modulus, `keyValid` is the conjunction of the checks an
implementation computes, with each remainder (`e d mod (p - 1)` and the
others) known only when its modulus is positive: when `p` or `q` is 0 or
1, `p q = n` fails anyway, as the other factor would have to be `n`, which
is longer. `p < n` and `q < n` need no check: `n ≥ 256^(k - 1)`.
-/

namespace VG.Proof.Rsa

open VG.Spec.Rsa

/-- The checks an implementation computes, from the remainders it computes
(`Rp1 = e d mod Mp`, …) and `Mp = p - 1`, `Mq = q - 1`, in its order. -/
def keyBits (n d p q dP dQ qInv Mp Mq Rp1 Rp2 Rq1 Rq2 Rpq : Nat) : Bool :=
  true && decide (d < n) && decide (p * q = n) &&
    decide (dP < Mp) && decide (Rp1 = 1) && decide (Rp2 = 1) &&
    decide (dQ < Mq) && decide (Rq1 = 1) && decide (Rq2 = 1) &&
    decide (qInv < p) && decide (Rpq = 1)

theorem factor_ge_two {n p q B : Nat} (h : p * q = n) (hq : q < B) (hB : B ≤ n) : 2 ≤ p := by
  rcases Nat.lt_or_ge p 2 with hp | hp
  · rcases (show p = 0 ∨ p = 1 by omega) with rfl | rfl
    · rw [Nat.zero_mul] at h; omega
    · rw [Nat.one_mul] at h; omega
  · exact hp

theorem keyValid_parts {k n e d p q dP dQ qInv : Nat} (hm : modulusValid n k = true) (he : exponentValid e = true)
    (hp : p < 256 ^ (k - 1)) (hq : q < 256 ^ (k - 1)) {Mp Mq Rp1 Rp2 Rq1 Rq2 Rpq : Nat}
    (hMp : 0 < p → Mp = p - 1) (hMq : 0 < q → Mq = q - 1)
    (hR1 : 0 < Mp → Rp1 = e * d % Mp) (hR2 : 0 < Mp → Rp2 = e * dP % Mp)
    (hR3 : 0 < Mq → Rq1 = e * d % Mq) (hR4 : 0 < Mq → Rq2 = e * dQ % Mq)
    (hR5 : 0 < p → Rpq = qInv * q % p) :
    keyValid k n e d p q dP dQ qInv = keyBits n d p q dP dQ qInv Mp Mq Rp1 Rp2 Rq1 Rq2 Rpq := by
  have hn : 256 ^ (k - 1) ≤ n := by
    simp only [modulusValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hm; exact hm.2
  rw [Bool.eq_iff_iff]
  simp only [keyValid, keyBits, hm, he, Bool.true_and, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    and_assoc]
  by_cases hpq : p * q = n
  · have hp2 := factor_ge_two hpq hq hn
    have hq2 := factor_ge_two (n := n) (q := p) (by rw [Nat.mul_comm]; exact hpq) hp hn
    have eMp := hMp (by omega)
    have eMq := hMq (by omega)
    rw [hR1 (by omega), hR2 (by omega), hR3 (by omega), hR4 (by omega), hR5 (by omega), eMp, eMq,
      Nat.mul_comm e d, Nat.mul_comm qInv q]
    constructor
    · rintro ⟨h1, -, -, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
      exact ⟨h1, h4, h7, h5, h8, h9, h6, h10, h11, h12⟩
    · rintro ⟨h1, h4, h7, h5, h8, h9, h6, h10, h11, h12⟩
      exact ⟨h1, by omega, by omega, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
  · constructor
    · rintro ⟨-, -, -, h, -⟩; exact absurd h hpq
    · rintro ⟨-, h, -⟩; exact absurd h hpq

end VG.Proof.Rsa
