module

public import VerifiedGarbage.Proof.Rsa.KeyCheckMath
import VerifiedGarbage.Proof.Rsa.KeyParts

/-!
# RSA: the key checks from products

The arithmetic behind checking a key with products instead of a division
(`Impl/Rsa/PPC64LE/MontKey.lean`):

* `mulLo_row`: a row of the schoolbook product truncated to `W = P Q`
  digits' worth: adding `x_i [y]` over the `Q` top digits' worth at digit
  `i` (`P = 2^(32 i)`), the carry dropped, gives the truncated sum.
* `mont_step`: a step of Montgomery's multiplication by operands: `T = A +
  x_i Y + k m` with `k = ((A + x_i Y) mod 2^32) (-m⁻¹) mod 2^32` is a
  multiple of `2^32`, and `T / 2^32` stays below `3 M` (below `2 m` when
  `Y < m`) for `m, Y < M`.
* `pq_eq_iff`: for an odd `p`, `p q = n` exactly when `p q ≡ n (mod W)` for
  a power of two `W` above `q` and `n`, and `p ∣ n`;
* `mont_zero_iff`, `mont_eq_iff`: Montgomery's results compared, for an odd
  modulus;
* `crtKeyValid_bitsM`, `keyValid_bitsM`: the checks so computed are the
  spec's.
-/

@[expose] public section

namespace VG.Proof.Rsa

open VG.Spec.Rsa

/-! ## The truncated product -/

/-- A row: `O = L + P H` (`L < P`, `H < Q`), `H' + Q c = H + x Y'` with `Y'`
the low digits of `Y` (`Y ≡ Y' (mod Q)`): `L + P H'` is `O + P x Y` modulo
`P Q`. -/
theorem mulLo_row {P Q L H H' c x Y Y' : Nat} (hP : 0 < P) (hL : L < P) (hH' : H' < Q)
    (hrow : H' + Q * c = H + x * Y') (hY : Y' % Q = Y % Q) :
    L + P * H' = (L + P * H + P * (x * Y)) % (P * Q) := by
  have hQ : 0 < Q := Nat.lt_of_le_of_lt (Nat.zero_le _) hH'
  have e1 : (H + x * Y) % Q = H' := by
    rw [Nat.add_mod, Nat.mul_mod, ← hY, ← Nat.mul_mod, ← Nat.add_mod, ← hrow, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hH']
  rw [← e1, show L + P * H + P * (x * Y) = L + P * (H + x * Y) by rw [Nat.mul_add, Nat.add_assoc]]
  rw [Nat.mod_mul, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hL, Nat.add_mul_div_left _ _ hP,
    Nat.div_eq_of_lt hL, Nat.zero_add]

/-! ## A step of Montgomery's multiplication -/

/-- `k` makes `T = S + k m` a multiple of `2^32`, for `m iv ≡ -1 (mod 2^32)`. -/
theorem mont_div {m iv S : Nat} (hinv : (m % 2 ^ 32 * iv + 1) % 2 ^ 32 = 0) :
    (S + S % 2 ^ 32 * iv % 2 ^ 32 * m) % 2 ^ 32 = 0 := by
  have e : S % 2 ^ 32 + S % 2 ^ 32 * iv * (m % 2 ^ 32) = S % 2 ^ 32 * (m % 2 ^ 32 * iv + 1) := by
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_assoc, Nat.mul_comm iv, Nat.add_comm]
  rw [Nat.add_mod, Nat.mul_mod (S % 2 ^ 32 * iv % 2 ^ 32), Nat.mod_mod, Nat.mod_mul_mod, Nat.add_mod_mod, e,
    Nat.mul_mod, hinv, Nat.mul_zero, Nat.zero_mod]

/-- The bounds of a step: below `3 M`, and below `2 m` from `A < 2 m` and `Y < m`. -/
theorem mont_bound {M m A Y x k : Nat} (hm : m < M) (hY : Y < M) (hA : A < 3 * M)
    (hx : x < 2 ^ 32) (hk : k < 2 ^ 32) :
    (A + x * Y + k * m) / 2 ^ 32 < 3 * M := by
  have e1 : x * Y ≤ (2 ^ 32 - 1) * M := Nat.mul_le_mul (by omega) (by omega)
  have e2 : k * m ≤ (2 ^ 32 - 1) * M := Nat.mul_le_mul (by omega) (by omega)
  rw [Nat.div_lt_iff_lt_mul (by decide)]
  omega

theorem mont_bound2 {m A Y x k : Nat} (hY : Y < m) (hA : A < 2 * m) (hx : x < 2 ^ 32) (hk : k < 2 ^ 32) :
    (A + x * Y + k * m) / 2 ^ 32 < 2 * m := by
  have e1 : x * Y ≤ (2 ^ 32 - 1) * m := Nat.mul_le_mul (by omega) (by omega)
  have e2 : k * m ≤ (2 ^ 32 - 1) * m := Nat.mul_le_mul (by omega) (by omega)
  rw [Nat.div_lt_iff_lt_mul (by decide)]
  omega

/-- The congruence of a step: `(T / 2^32) 2^(32 (i + 1)) ≡ X' Y`, from
`A 2^(32 i) ≡ X Y` and `X' = X + 2^(32 i) x`. -/
theorem mont_cong {m A Y x k X i : Nat} (hT : (A + x * Y + k * m) % 2 ^ 32 = 0)
    (hA : A * 2 ^ (32 * i) % m = X * Y % m) :
    (A + x * Y + k * m) / 2 ^ 32 * 2 ^ (32 * (i + 1)) % m = (X + 2 ^ (32 * i) * x) * Y % m := by
  have e : (A + x * Y + k * m) / 2 ^ 32 * 2 ^ (32 * (i + 1)) = (A + x * Y + k * m) * 2 ^ (32 * i) := by
    rw [show 32 * (i + 1) = 32 + 32 * i by omega, Nat.pow_add, ← Nat.mul_assoc,
      Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hT)]
  rw [e, Nat.add_mul, Nat.add_mul, Nat.add_mod, Nat.add_mod (A * _), hA,
    show k * m * 2 ^ (32 * i) = m * (k * 2 ^ (32 * i)) by ac_rfl, Nat.mul_mod_right, Nat.add_zero,
    Nat.mod_mod, ← Nat.add_mod, Nat.add_mul (X), show x * Y * 2 ^ (32 * i) = 2 ^ (32 * i) * x * Y by ac_rfl]

/-! ## The comparisons -/

theorem coprime_pow2 {p j : Nat} (hp : p % 2 = 1) : Nat.Coprime p (2 ^ j) := by
  apply Nat.Coprime.pow_right
  rw [Nat.coprime_comm, Nat.Coprime, Nat.gcd_rec, hp, Nat.gcd_one_left]

/-- For an odd `p` and `W` a power of two above `q` and `n`: `p q = n` exactly
when `p q ≡ n (mod W)` and `p ∣ n`. -/
theorem pq_eq_iff {p q n j : Nat} (hp : p % 2 = 1) (hq : q < 2 ^ j) (hn : n < 2 ^ j) :
    p * q = n ↔ p * q % 2 ^ j = n ∧ n % p = 0 := by
  constructor
  · rintro rfl; exact ⟨Nat.mod_eq_of_lt hn, Nat.mul_mod_right _ _⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨k, rfl⟩ := Nat.dvd_of_mod_eq_zero h2
    have hk : k < 2 ^ j := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left _ (by omega)) hn
    have e : p * q % 2 ^ j = p * k % 2 ^ j := by rw [h1, Nat.mod_eq_of_lt hn]
    have cp := (coprime_pow2 (j := j) hp).symm
    have d1 : 2 ^ j ∣ q - k := cp.dvd_of_dvd_mul_left (by
      rw [Nat.mul_sub]; exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq e))
    have d2 : 2 ^ j ∣ k - q := cp.dvd_of_dvd_mul_left (by
      rw [Nat.mul_sub]; exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq e.symm))
    have z1 := Nat.eq_zero_of_dvd_of_lt d1 (by omega)
    have z2 := Nat.eq_zero_of_dvd_of_lt d2 (by omega)
    rw [show q = k by omega]

/-- Montgomery's result `M < m` with `M 2^j ≡ n` is zero exactly when `m ∣ n`. -/
theorem mont_zero_iff {m M n j : Nat} (hm : m % 2 = 1) (hM : M < m) (h : M * 2 ^ j % m = n % m) :
    M = 0 ↔ n % m = 0 := by
  constructor
  · rintro rfl; rw [← h, Nat.zero_mul, Nat.zero_mod]
  · intro hn
    rw [hn] at h
    have : m ∣ M * 2 ^ j := Nat.dvd_of_mod_eq_zero h
    have := (Nat.Coprime.dvd_of_dvd_mul_right (coprime_pow2 hm) this)
    exact Nat.eq_zero_of_dvd_of_lt this hM

/-- Montgomery's results `M₁, M₂ < m` with `M₁ 2^j ≡ a` and `M₂ 2^j ≡ 1` are
equal exactly when `a ≡ 1 (mod m)`, for `m ≥ 2`. -/
theorem mont_eq_iff {m M₁ M₂ a j : Nat} (hm : m % 2 = 1) (hm2 : 2 ≤ m) (h₁ : M₁ < m) (h₂ : M₂ < m)
    (e₁ : M₁ * 2 ^ j % m = a % m) (e₂ : M₂ * 2 ^ j % m = 1 % m) :
    M₁ = M₂ ↔ a % m = 1 := by
  rw [Nat.mod_eq_of_lt (show 1 < m by omega)] at e₂
  constructor
  · rintro rfl; rw [← e₁, e₂]
  · intro ha
    have e : M₁ * 2 ^ j % m = M₂ * 2 ^ j % m := by rw [e₁, e₂, ha]
    have cp := coprime_pow2 (j := j) hm
    have d1 : m ∣ M₁ - M₂ := cp.dvd_of_dvd_mul_right (by
      rw [Nat.sub_mul]; exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq e))
    have d2 : m ∣ M₂ - M₁ := cp.dvd_of_dvd_mul_right (by
      rw [Nat.sub_mul]; exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq e.symm))
    have z1 := Nat.eq_zero_of_dvd_of_lt d1 (by omega)
    have z2 := Nat.eq_zero_of_dvd_of_lt d2 (by omega)
    omega

/-- With `L = p q mod W` and `M` Montgomery's `n` (zero exactly when `p ∣ n`
for an odd `p ≥ 2`), the checks `p` odd, `L = n`, `M = 0` are those of
`n / p = q` and `n mod p = 0`, for `q < n` and `q, n` below `W`. -/
theorem maskM_iff {P Q N L M V j : Nat} (hQN : Q < N) (hqj : Q < 2 ^ j) (hnj : N < 2 ^ j)
    (hL : L = P * Q % 2 ^ j) (hM : P % 2 = 1 → 2 ≤ P → (M = 0 ↔ N % P = 0)) :
    (P % 2 = 1 ∧ L = N ∧ M = 0 ∧ V = 1) ↔ (P % 2 = 1 ∧ N / P = Q ∧ N % P = 0 ∧ V = 1) := by
  constructor
  · rintro ⟨podd, h1, h2, h3⟩
    by_cases p2 : 2 ≤ P
    · have hpq := (pq_eq_iff podd hqj hnj).2 ⟨by rw [← hL, h1], (hM podd p2).1 h2⟩
      refine ⟨podd, ?_, by rw [← hpq, Nat.mul_mod_right], h3⟩
      rw [← hpq, Nat.mul_div_cancel_left _ (by omega)]
    · have p1 : P = 1 := by omega
      subst p1; rw [Nat.one_mul, Nat.mod_eq_of_lt hqj] at hL; omega
  · rintro ⟨podd, h1, h2, h3⟩
    have hpq : P * Q = N := mul_of_div h1 h2
    have p2 : 2 ≤ P := by
      rcases Nat.lt_or_ge P 2 with hp | hp
      · have p1 : P = 1 := by omega
        subst p1; rw [Nat.one_mul] at hpq; omega
      · exact hp
    exact ⟨podd, by rw [hL, hpq, Nat.mod_eq_of_lt hnj], (hM podd p2).2 h2, h3⟩

/-! ## The checks -/

/-- The checks of `crtKeyValid` in the order the code computes them, from the
product `L = p q mod W`, Montgomery's `M ≡ n` modulo `p`, the products `R₁`,
`R₂` of `e dP` and `e dQ` modulo `p - 1` and `q - 1`, and Montgomery's
`A₁ ≡ q qInv` and `A₂ ≡ 1` modulo `p`. -/
def crtBitsM (n p q dP dQ qInv L M R₁ R₂ A₁ A₂ : Nat) : Bool :=
  decide (p % 2 = 1) && decide (L = n) && decide (M = 0) && decide (dP < 2 * (p / 2)) &&
    decide (R₁ = 1) && decide (dQ < 2 * (q / 2)) && decide (R₂ = 1) && decide (qInv < p) &&
    decide (A₁ = A₂)

/-- Then those of `d`. -/
def keyBitsM (n d p q dP dQ qInv L M R₁ R₂ A₁ A₂ Y₁ Y₂ : Nat) : Bool :=
  crtBitsM n p q dP dQ qInv L M R₁ R₂ A₁ A₂ && decide (d < n) && decide (Y₁ = dP) && decide (Y₂ = dQ)

theorem crtKeyValid_bitsM {k n e p q dP dQ qInv j : Nat} (hm : modulusValid n k = true)
    (he : exponentValid e = true) (hp : p < 256 ^ (k - 1)) (hq : q < 256 ^ (k - 1))
    (hqj : q < 2 ^ j) (hnj : n < 2 ^ j)
    {L M R₁ R₂ A₁ A₂ : Nat} (hL : L = p * q % 2 ^ j)
    (hM : p % 2 = 1 → 2 ≤ p → (M = 0 ↔ n % p = 0))
    (hR₁ : dP < 2 * (p / 2) → R₁ = e * dP % (2 * (p / 2)))
    (hR₂ : dQ < 2 * (q / 2) → R₂ = e * dQ % (2 * (q / 2)))
    (hA : qInv < p → p % 2 = 1 → 2 ≤ p → (A₁ = A₂ ↔ q * qInv % p = 1)) :
    crtKeyValid k n e p q dP dQ qInv = crtBitsM n p q dP dQ qInv L M R₁ R₂ A₁ A₂ := by
  obtain ⟨hodd, hn⟩ := modulusValid_facts hm
  rw [Bool.eq_iff_iff]
  simp only [crtKeyValid, crtBitsM, hm, he, Bool.true_and, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    and_assoc]
  by_cases hpq : p * q = n
  · have p2 := factor_ge_two hpq hq hn
    have q2 := factor_ge_two (n := n) (q := p) (by rw [Nat.mul_comm]; exact hpq) hp hn
    have podd := odd_factor hpq hodd
    have qodd := odd_factor (by rw [Nat.mul_comm]; exact hpq) hodd
    obtain ⟨e1, e2⟩ := (pq_eq_iff podd hqj hnj).1 hpq
    have eqL : L = n := by rw [hL, e1]
    have eqM : M = 0 := (hM podd p2).2 e2
    have mp : 2 * (p / 2) = p - 1 := by omega
    have mq : 2 * (q / 2) = q - 1 := by omega
    rw [mp] at hR₁ ⊢
    rw [mq] at hR₂ ⊢
    constructor
    · rintro ⟨-, h1, h2, h3, h4, h5, h6⟩
      exact ⟨podd, eqL, eqM, h1, by rw [hR₁ h1]; exact h2, h3, by rw [hR₂ h3]; exact h4, h5,
        (hA h5 podd p2).2 h6⟩
    · rintro ⟨-, -, -, h1, h2, h3, h4, h5, h6⟩
      exact ⟨hpq, h1, by rw [← hR₁ h1]; exact h2, h3, by rw [← hR₂ h3]; exact h4, h5,
        (hA h5 podd p2).1 h6⟩
  · constructor
    · rintro ⟨h, -⟩; exact absurd h hpq
    · rintro ⟨podd, h1, h2, -⟩
      by_cases p2 : 2 ≤ p
      · exact absurd ((pq_eq_iff podd hqj hnj).2 ⟨by rw [← hL, h1], (hM podd p2).1 h2⟩) hpq
      · have p1 : p = 1 := by omega
        subst p1
        rw [Nat.one_mul, Nat.mod_eq_of_lt hqj] at hL
        have : q < n := Nat.lt_of_lt_of_le hq hn
        omega

theorem keyValid_bitsM {k n e d p q dP dQ qInv j : Nat} (hm : modulusValid n k = true)
    (he : exponentValid e = true) (hp : p < 256 ^ (k - 1)) (hq : q < 256 ^ (k - 1))
    (hqj : q < 2 ^ j) (hnj : n < 2 ^ j)
    {L M R₁ R₂ A₁ A₂ Y₁ Y₂ : Nat} (hL : L = p * q % 2 ^ j)
    (hM : p % 2 = 1 → 2 ≤ p → (M = 0 ↔ n % p = 0))
    (hR₁ : dP < 2 * (p / 2) → R₁ = e * dP % (2 * (p / 2)))
    (hR₂ : dQ < 2 * (q / 2) → R₂ = e * dQ % (2 * (q / 2)))
    (hA : qInv < p → p % 2 = 1 → 2 ≤ p → (A₁ = A₂ ↔ q * qInv % p = 1))
    (hY₁ : 0 < 2 * (p / 2) → Y₁ = d % (2 * (p / 2))) (hY₂ : 0 < 2 * (q / 2) → Y₂ = d % (2 * (q / 2))) :
    keyValid k n e d p q dP dQ qInv = keyBitsM n d p q dP dQ qInv L M R₁ R₂ A₁ A₂ Y₁ Y₂ := by
  rw [keyValid_crt hm hp hq, crtKeyValid_bitsM hm he hp hq hqj hnj hL hM hR₁ hR₂ hA, keyBitsM]
  by_cases hc : crtBitsM n p q dP dQ qInv L M R₁ R₂ A₁ A₂ = true
  · have hv := hc
    rw [← crtKeyValid_bitsM hm he hp hq hqj hnj hL hM hR₁ hR₂ hA] at hv
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
