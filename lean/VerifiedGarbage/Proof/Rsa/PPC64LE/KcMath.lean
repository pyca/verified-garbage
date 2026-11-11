module

public import VerifiedGarbage.Proof.Rsa.KeyCheckMath
public import VerifiedGarbage.Proof.Rsa.MontCheckMath
public import VerifiedGarbage.Spec.Rsa
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Framework.PowLit

/-! # The checks of an RSA key on PPC64LE: the mask is the spec's

`ck_bits`: with the products as `mulMod` computes them (`e` over 33 bits,
`q` over all its bits, each known when its factor is below its modulus and
twice the modulus fits), the mask the checks compute is `keyValid`.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.KeyCheck

open VG.Spec.Rsa

theorem fit_two {k w p : Nat} (hk : 1 ≤ k) (hw : 256 ^ k ≤ 2 ^ (32 * w)) (hp : p < 256 ^ (k - 1)) :
    2 * p ≤ 2 ^ (32 * w) := by
  have : 256 ^ k = 256 * 256 ^ (k - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  omega

theorem ck_bits {k n e d p q dP dQ qI w : Nat} (hm : modulusValid n k = true) (he : exponentValid e = true)
    (hp : p < 256 ^ (k - 1)) (hq : q < 256 ^ (k - 1)) (hk : 1 ≤ k) (hw : 256 ^ k ≤ 2 ^ (32 * w))
    {X₁ X₂ R₁ R₂ R₃ Y₁ Y₂ : Nat} (hX : 0 < p → X₁ = n / p ∧ X₂ = n % p)
    (hR₁ : dP < 2 * (p / 2) → 2 * (2 * (p / 2)) ≤ 2 ^ (32 * w) → R₁ = e % 2 ^ 33 * dP % (2 * (p / 2)))
    (hR₂ : dQ < 2 * (q / 2) → 2 * (2 * (q / 2)) ≤ 2 ^ (32 * w) → R₂ = e % 2 ^ 33 * dQ % (2 * (q / 2)))
    (hR₃ : qI < p → 2 * p ≤ 2 ^ (32 * w) → R₃ = q * qI % p)
    (hY₁ : 0 < 2 * (p / 2) → Y₁ = d % (2 * (p / 2))) (hY₂ : 0 < 2 * (q / 2) → Y₂ = d % (2 * (q / 2))) :
    keyValid k n e d p q dP dQ qI = VG.Proof.Rsa.keyBits' n d p q dP dQ qI X₁ X₂ R₁ R₂ R₃ Y₁ Y₂ := by
  have he' : e < 2 ^ 33 := by
    simp only [exponentValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at he; exact he.2
  have fp := fit_two hk hw hp
  have fq := fit_two hk hw hq
  refine VG.Proof.Rsa.keyValid_bits hm he hp hq hX (fun h => ?_) (fun h => ?_) (fun h => ?_) hY₁ hY₂
  · rw [hR₁ h (Nat.le_trans (by omega : 2 * (2 * (p / 2)) ≤ 2 * p) fp), Nat.mod_eq_of_lt he']
  · rw [hR₂ h (Nat.le_trans (by omega : 2 * (2 * (q / 2)) ≤ 2 * q) fq), Nat.mod_eq_of_lt he']
  · rw [hR₃ h fp]

/-- `ck_bits` for the checks by products: `p q mod 2^(32 w)`, Montgomery's
`n` modulo `p`, and Montgomery's `q qInv` and `1` compared. -/
theorem ck_bitsM {k n e d p q dP dQ qI w : Nat} (hm : modulusValid n k = true) (he : exponentValid e = true)
    (hn : n < 256 ^ k) (hp : p < 256 ^ (k - 1)) (hq : q < 256 ^ (k - 1)) (hk : 1 ≤ k) (hw : 256 ^ k ≤ 2 ^ (32 * w))
    {L M R₁ R₂ A₁ A₂ Y₁ Y₂ : Nat} (hL : L = p * q % 2 ^ (32 * w))
    (hM : p % 2 = 1 → 2 ≤ p → (M = 0 ↔ n % p = 0))
    (hR₁ : dP < 2 * (p / 2) → 2 * (2 * (p / 2)) ≤ 2 ^ (32 * w) → R₁ = e % 2 ^ 33 * dP % (2 * (p / 2)))
    (hR₂ : dQ < 2 * (q / 2) → 2 * (2 * (q / 2)) ≤ 2 ^ (32 * w) → R₂ = e % 2 ^ 33 * dQ % (2 * (q / 2)))
    (hA : qI < p → p % 2 = 1 → 2 ≤ p → (A₁ = A₂ ↔ q * qI % p = 1))
    (hY₁ : 0 < 2 * (p / 2) → Y₁ = d % (2 * (p / 2))) (hY₂ : 0 < 2 * (q / 2) → Y₂ = d % (2 * (q / 2))) :
    keyValid k n e d p q dP dQ qI = VG.Proof.Rsa.keyBitsM n d p q dP dQ qI L M R₁ R₂ A₁ A₂ Y₁ Y₂ := by
  have he' : e < 2 ^ 33 := by
    simp only [exponentValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at he; exact he.2
  have fp := fit_two hk hw hp
  have fq := fit_two hk hw hq
  have hk1 : 256 ^ (k - 1) ≤ 256 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
  refine VG.Proof.Rsa.keyValid_bitsM (j := 32 * w) hm he hp hq (by omega) (by omega) hL hM (fun h => ?_)
    (fun h => ?_) hA hY₁ hY₂
  · rw [hR₁ h (Nat.le_trans (by omega : 2 * (2 * (p / 2)) ≤ 2 * p) fp), Nat.mod_eq_of_lt he']
  · rw [hR₂ h (Nat.le_trans (by omega : 2 * (2 * (q / 2)) ≤ 2 * q) fq), Nat.mod_eq_of_lt he']

/-- A number of `l < k` bytes is below `256^(k - 1)`. -/
theorem lt_pow_of_len (bs : List Byte) {k : Nat} (h : bs.length < k) : os2ip bs < 256 ^ (k - 1) :=
  Nat.lt_of_lt_of_le (VG.Proof.Rsa.lt_of_os2ip bs) (Nat.pow_le_pow_right (by decide) (by omega))

/-- A number of `k` bytes is below `256^k`. -/
theorem lt_pow_len (bs : List Byte) {k : Nat} (h : bs.length = k) : os2ip bs < 256 ^ k := by
  rw [← h]; exact VG.Proof.Rsa.lt_of_os2ip bs

/-- A number of `a` bytes is below `2^(8 a)`. -/
theorem lt_pow8_of_len (bs : List Byte) {a : Nat} (h : bs.length = a) : os2ip bs < 2 ^ (8 * a) := by
  rw [Nat.pow_mul, ← h]; exact VG.Proof.Rsa.lt_of_os2ip bs

/-- `2^(32 w)` for `w = ⌈k / 4⌉` is at least `256^k`. -/
theorem pow_kw (k : Nat) : 256 ^ k ≤ 2 ^ (32 * ((k + 3) / 4)) := by
  rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]
  exact Nat.pow_le_pow_right (by decide) (by omega)

/-! ## Balanced keys -/

/-- A balanced key of full words: `p_len` a multiple of 8 and at least 32,
`q_len` and `2 w` equal to it. -/
def Shape (w pL qL : Nat) : Prop := pL % 8 = 0 ∧ 2 * w = pL ∧ pL = qL ∧ 32 ≤ pL

instance (w pL qL : Nat) : Decidable (Shape w pL qL) := by unfold Shape; infer_instance

/-- For a balanced key with `p q = n`, `n`'s first byte not zero and
`w = ⌈k / 4⌉`, `p - 1`'s top word (of `w / 4`) is not zero. -/
theorem shape_bound {w k pL qL n p q : Nat} (hs : Shape w pL qL) (hwk : w = (k + 3) / 4) (hpq : p * q = n)
    (hn : 256 ^ (k - 1) ≤ n) (hq : q < 2 ^ (8 * qL)) : 2 ^ (64 * (w / 4 - 1)) ≤ 2 * (p / 2) := by
  obtain ⟨p8, hpw, hpq', p32⟩ := hs
  have hk : 2 * pL - 4 ≤ k - 1 := by omega
  have e1 : (2 : Nat) ^ (16 * pL - 32) = 2 ^ (8 * pL - 32) * 2 ^ (8 * pL) := by
    rw [← Nat.pow_add]; congr 1; omega
  have hn' : 2 ^ (16 * pL - 32) ≤ n := by
    refine Nat.le_trans ?_ hn
    rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  rw [show 8 * qL = 8 * pL by omega] at hq
  have hp : 2 ^ (8 * pL - 32) < p := by
    rcases Nat.lt_or_ge (2 ^ (8 * pL - 32)) p with h | h
    · exact h
    · rcases Nat.eq_zero_or_pos p with h0 | h0
      · subst h0; rw [Nat.zero_mul] at hpq; have := Nat.two_pow_pos (16 * pL - 32); omega
      · have := Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_left hq h0) (Nat.mul_le_mul_right _ h)
        omega
  have e3 : 2 ^ (64 * (w / 4 - 1)) ≤ 2 ^ (8 * pL - 32) := Nat.pow_le_pow_right (by decide) (by omega)
  omega

/-- The checks' bits but for the remainders, which matter only once `p` is
odd, `L = n` and `M = 0`. -/
theorem keyBitsM_congr {n d p q dP dQ qI L M R₁ R₂ A₁ A₂ Y₁ Y₂ Y₁' Y₂' : Nat}
    (h : p % 2 = 1 → L = n → M = 0 → Y₁ = Y₁' ∧ Y₂ = Y₂') :
    VG.Proof.Rsa.keyBitsM n d p q dP dQ qI L M R₁ R₂ A₁ A₂ Y₁ Y₂ =
      VG.Proof.Rsa.keyBitsM n d p q dP dQ qI L M R₁ R₂ A₁ A₂ Y₁' Y₂' := by
  unfold VG.Proof.Rsa.keyBitsM VG.Proof.Rsa.crtBitsM
  by_cases h1 : p % 2 = 1
  · by_cases h2 : L = n
    · by_cases h3 : M = 0
      · obtain ⟨e1, e2⟩ := h h1 h2 h3; rw [e1, e2]
      · simp [h3]
    · simp [h2]
  · simp [h1]

/-- `p` odd, `L = n` and `M = 0` are `p q = n`. -/
theorem pq_of_bits {n p q L M j : Nat} (hqj : q < 2 ^ j) (hnj : n < 2 ^ j) (hL : L = p * q % 2 ^ j)
    (hM : p % 2 = 1 → 2 ≤ p → (M = 0 ↔ n % p = 0)) (h1 : p % 2 = 1) (h2 : L = n) (h3 : M = 0) : p * q = n := by
  rcases (show p = 1 ∨ 2 ≤ p by omega) with e | e
  · subst e; rw [Nat.one_mul] at hL ⊢; rw [hL, Nat.mod_eq_of_lt hqj] at h2; exact h2
  · exact (VG.Proof.Rsa.pq_eq_iff h1 hqj hnj).2 ⟨by rw [← hL, h2], (hM h1 e).1 h3⟩

/-- `ck_bitsM` with the remainders exact only when the divisor's top word
(of `k / 16`) is not zero, for a balanced key. -/
theorem ck_bitsM' {k n e d p q dP dQ qI w pL qL : Nat} (hwk : w = (k + 3) / 4) (hm : modulusValid n k = true)
    (he : exponentValid e = true) (hn : n < 256 ^ k) (hp : p < 256 ^ (k - 1)) (hq : q < 256 ^ (k - 1))
    (hk : 1 ≤ k) (hw : 256 ^ k ≤ 2 ^ (32 * w)) (hpL : p < 2 ^ (8 * pL)) (hqL : q < 2 ^ (8 * qL))
    {L M R₁ R₂ A₁ A₂ Y₁ Y₂ : Nat} (hL : L = p * q % 2 ^ (32 * w))
    (hM : p % 2 = 1 → 2 ≤ p → (M = 0 ↔ n % p = 0))
    (hR₁ : dP < 2 * (p / 2) → 2 * (2 * (p / 2)) ≤ 2 ^ (32 * w) → R₁ = e % 2 ^ 33 * dP % (2 * (p / 2)))
    (hR₂ : dQ < 2 * (q / 2) → 2 * (2 * (q / 2)) ≤ 2 ^ (32 * w) → R₂ = e % 2 ^ 33 * dQ % (2 * (q / 2)))
    (hA : qI < p → p % 2 = 1 → 2 ≤ p → (A₁ = A₂ ↔ q * qI % p = 1))
    (hY₁ : 0 < 2 * (p / 2) → (Shape w pL qL → 2 ^ (64 * (w / 4 - 1)) ≤ 2 * (p / 2)) →
      Y₁ = d % (2 * (p / 2)))
    (hY₂ : 0 < 2 * (q / 2) → (Shape w pL qL → 2 ^ (64 * (w / 4 - 1)) ≤ 2 * (q / 2)) →
      Y₂ = d % (2 * (q / 2))) :
    keyValid k n e d p q dP dQ qI = VG.Proof.Rsa.keyBitsM n d p q dP dQ qI L M R₁ R₂ A₁ A₂ Y₁ Y₂ := by
  have hnv := (VG.Proof.Rsa.modulusValid_facts hm).2
  have hk1 : 256 ^ (k - 1) ≤ 256 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
  have hqj : q < 2 ^ (32 * w) := by omega
  have hnj : n < 2 ^ (32 * w) := by omega
  rw [keyBitsM_congr (Y₁' := if 0 < 2 * (p / 2) then d % (2 * (p / 2)) else Y₁)
    (Y₂' := if 0 < 2 * (q / 2) then d % (2 * (q / 2)) else Y₂) fun h1 h2 h3 => ?_]
  · exact ck_bitsM hm he hn hp hq hk hw hL hM hR₁ hR₂ hA (fun h => by rw [ite_eq_left h])
      (fun h => by rw [ite_eq_left h])
  · have pq := pq_of_bits hqj hnj hL hM h1 h2 h3
    constructor
    · by_cases h0 : 0 < 2 * (p / 2)
      · rw [ite_eq_left h0]; exact hY₁ h0 fun hs => shape_bound hs hwk pq hnv hqL
      · rw [ite_eq_right h0]
    · by_cases h0 : 0 < 2 * (q / 2)
      · rw [ite_eq_left h0]
        refine hY₂ h0 fun hs => ?_
        have hs' : Shape w qL pL := ⟨by have := hs.1; have := hs.2.2.1; omega, by have := hs.2.1; have := hs.2.2.1; omega,
          hs.2.2.1.symm, by have := hs.2.2.2; have := hs.2.2.1; omega⟩
        exact shape_bound hs' hwk (by rw [Nat.mul_comm]; exact pq) hnv hpL
      · rw [ite_eq_right h0]

end VG.Proof.Rsa.PPC64LE.KeyCheck
