import VerifiedGarbage.Proof.Framework.PowLit
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Find
import Mathlib.Data.Finset.Card

/-!
# Pratt certificates

Primality by Lucas's theorem (`lucas`): for a prime `p` of a certificate
tree, a witness `a` of order `p - 1` modulo `p` and the prime factors of
`p - 1` (with multiplicity), each proven prime in turn (`prime_of_cert`),
down to factors below `2^16`, prime by trial division (`prime_small`). The
kernel evaluates the modular powers with `powMod`, a binary exponentiation on
`Nat`, and the trial divisions (`decide +kernel`).

Lucas's theorem is proven here on `Nat`, by counting the powers of `a`
modulo `p`, rather than taken from `Mathlib.NumberTheory.LucasPrimality`,
whose algebra (`ZMod`, orders in groups) every module that imports a curve's
prime proof would load (`ci/check_lean_speed.py`). `PrattZMod.lean` casts
`powMod` to `ZMod` for the proofs that need it.
-/

namespace VG.Proof.Pratt

/-- `b^e % m` for `e < 2^n`, by binary exponentiation. -/
def powMod (m : Nat) : Nat → Nat → Nat → Nat
  | 0, _, _ => 1
  | n + 1, b, e => if e = 0 then 1 else
      if e % 2 = 0 then powMod m n (b * b % m) (e / 2) else b * powMod m n (b * b % m) (e / 2) % m

theorem powMod_eq (m : Nat) (hm : 1 < m) (n b e : Nat) (he : e < 2 ^ n) : powMod m n b e = b ^ e % m := by
  induction n generalizing b e with
  | zero =>
    have : e = 0 := by simpa using he
    subst this; simp [powMod, Nat.mod_eq_of_lt hm]
  | succ n ih =>
    by_cases h0 : e = 0
    · subst h0; simp [powMod, Nat.mod_eq_of_lt hm]
    have he2 : e / 2 < 2 ^ n := by rw [Nat.pow_succ] at he; omega
    have hsplit : b ^ e = (b * b) ^ (e / 2) * b ^ (e % 2) := by
      rw [← Nat.pow_two, ← Nat.pow_mul, ← Nat.pow_add]; congr 1; omega
    by_cases h2 : e % 2 = 0
    · simp only [powMod, h0, h2, ite_false, ite_true]
      rw [ih _ _ he2, hsplit, h2, Nat.pow_zero, Nat.mul_one, ← Nat.pow_mod]
    · simp only [powMod, h0, h2, ite_false]
      have h1 : e % 2 = 1 := by omega
      rw [ih _ _ he2, hsplit, h1, Nat.pow_one, ← Nat.pow_mod, Nat.mul_mod_mod, Nat.mul_comm]

theorem prime_of_dvd_prod {q : Nat} (hq : q.Prime) {fs : List Nat} (hfs : ∀ f ∈ fs, f.Prime)
    (h : q ∣ fs.prod) : q ∈ fs := by
  induction fs with
  | nil => exact absurd (Nat.eq_one_of_dvd_one (by simpa using h)) hq.ne_one
  | cons f fs ih =>
    rw [List.prod_cons] at h
    rcases (Nat.Prime.dvd_mul hq).mp h with h | h
    · rw [(Nat.prime_dvd_prime_iff_eq hq (hfs f (by simp))).mp h]; simp
    · exact List.mem_cons_of_mem _ (ih (fun g hg => hfs g (List.mem_cons_of_mem _ hg)) h)

/-- `a^e % p = 1`, and so of every multiple of `e`. -/
theorem pow_mul_mod_one {a e p : Nat} (hp : 1 < p) (h : a ^ e % p = 1) (q : Nat) :
    a ^ (e * q) % p = 1 := by
  rw [Nat.pow_mul, Nat.pow_mod, h, Nat.one_pow]
  exact Nat.mod_eq_of_lt hp

theorem pow_add_mod {a e r p : Nat} (h : a ^ e % p = 1) : a ^ (e + r) % p = a ^ r % p := by
  rw [Nat.pow_add, Nat.mul_mod, h, Nat.one_mul, Nat.mod_mod]

/-- `a` is a unit modulo `p` if a positive power of it is 1. -/
theorem coprime_of_pow {a e p : Nat} (he : 0 < e) (h : a ^ e % p = 1) : Nat.Coprime a p := by
  have h1 : Nat.gcd a p ∣ a ^ e := Nat.dvd_trans (Nat.gcd_dvd_left a p)
    (Dvd.intro (a ^ (e - 1)) (by rw [← Nat.pow_succ']; congr 1; omega))
  have h2 : Nat.gcd a p ∣ a ^ e % p :=
    (Nat.dvd_mod_iff (Nat.gcd_dvd_right a p)).mpr h1
  rw [h] at h2
  exact Nat.eq_one_of_dvd_one h2

/-- `x % p = 1` if `p ∣ x - 1`, for `x ≥ 1` and `p > 1`. -/
theorem mod_eq_one_of_dvd {x p : Nat} (hx : 1 ≤ x) (hp : 1 < p) (h : p ∣ x - 1) : x % p = 1 := by
  obtain ⟨t, ht⟩ := h
  rw [show x = p * t + 1 by omega, Nat.mul_add_mod, Nat.mod_eq_of_lt hp]

/-- Lucas's theorem: if `a^(p-1) ≡ 1` and no `a^((p-1)/q)` for a prime
`q ∣ p - 1` is, then `p` is prime. -/
theorem lucas {p a : Nat} (hp : 2 ≤ p) (ha : a ^ (p - 1) % p = 1)
    (hq : ∀ q, q.Prime → q ∣ p - 1 → a ^ ((p - 1) / q) % p ≠ 1) : p.Prime := by
  have hex : ∃ k, 0 < k ∧ a ^ k % p = 1 := ⟨p - 1, by omega, ha⟩
  have hk : 0 < Nat.find hex ∧ a ^ Nat.find hex % p = 1 := Nat.find_spec hex
  have hmin : ∀ j, 0 < j → j < Nat.find hex → a ^ j % p ≠ 1 := fun j hj hjk h =>
    Nat.find_min hex hjk ⟨hj, h⟩
  generalize Nat.find hex = k at hk hmin
  -- The order `k` divides `p - 1`.
  have hdvd : k ∣ p - 1 := by
    have e := Nat.div_add_mod (p - 1) k
    have hr : a ^ ((p - 1) % k) % p = 1 := by
      rw [← pow_add_mod (pow_mul_mod_one (by omega) hk.2 ((p - 1) / k)), e]; exact ha
    refine Nat.dvd_of_mod_eq_zero (Classical.byContradiction fun h0 => ?_)
    exact hmin _ (Nat.pos_of_ne_zero h0) (Nat.mod_lt _ hk.1) hr
  -- It is `p - 1`: else a prime factor `q` of `(p - 1) / k` has `k ∣ (p - 1) / q`.
  have hkp : k = p - 1 := by
    refine Classical.byContradiction fun hne => ?_
    have hlt : k < p - 1 := Nat.lt_of_le_of_ne (Nat.le_of_dvd (by omega) hdvd) hne
    obtain ⟨m, hm⟩ := hdvd
    have hm1 : m ≠ 1 := fun h => by rw [h, Nat.mul_one] at hm; omega
    have hq' := Nat.minFac_prime hm1
    obtain ⟨r, hr⟩ := Nat.minFac_dvd m
    generalize m.minFac = q at hq' hr
    subst hr
    have hqd : q ∣ p - 1 := ⟨k * r, by rw [hm, Nat.mul_left_comm]⟩
    have hdiv : (p - 1) / q = k * r := by
      rw [hm, Nat.mul_left_comm, Nat.mul_div_cancel_left _ hq'.pos]
    have := hq _ hq' hqd
    rw [hdiv] at this
    exact this (pow_mul_mod_one (by omega) hk.2 r)
  subst hkp
  have hcop : Nat.Coprime a p := coprime_of_pow hk.1 hk.2
  have ha1 : 1 ≤ a := Nat.pos_of_ne_zero fun h => by
    rw [h, Nat.coprime_zero_left] at hcop; omega
  -- The powers `a^i`, `i < p - 1`, are distinct modulo `p`.
  have hinj : ∀ i < p - 1, ∀ j < p - 1, i < j → a ^ i % p ≠ a ^ j % p := by
    intro i _ j hj hij h
    have hd : p ∣ (a ^ (j - i) - 1) * a ^ i := by
      have := Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq h.symm)
      rwa [show a ^ j = a ^ (j - i) * a ^ i by rw [← Nat.pow_add, Nat.sub_add_cancel hij.le],
        ← Nat.sub_one_mul] at this
    have hd' := Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_left i hcop).symm hd
    exact hmin (j - i) (by omega) (by omega)
      (mod_eq_one_of_dvd (Nat.one_le_pow _ _ ha1) (by omega) hd')
  -- So the units modulo `p` are all of `1, …, p - 1`, and `p` is prime.
  let T := (Finset.range p).filter (fun r => Nat.Coprime r p)
  have hcard : p - 1 ≤ T.card := by
    have := Finset.card_le_card_of_injOn (s := Finset.range (p - 1)) (t := T) (fun i => a ^ i % p)
      (fun i _ => by
        simp only [T, Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq]
        refine ⟨Nat.mod_lt _ (by omega), ?_⟩
        rw [Nat.Coprime, ← Nat.gcd_rec, Nat.gcd_comm]
        exact Nat.Coprime.pow_left i hcop)
      (fun i hi j hj h => by
        simp only [Finset.coe_range, Set.mem_Iio] at hi hj
        rcases Nat.lt_trichotomy i j with hl | rfl | hl
        · exact absurd h (hinj i hi j hj hl)
        · rfl
        · exact absurd h.symm (hinj j hj i hi hl))
    simpa using this
  refine Nat.prime_def.mpr ⟨hp, fun m hm => ?_⟩
  refine Classical.byContradiction fun hne => ?_
  have hm0 : 0 < m := Nat.pos_of_dvd_of_pos hm (by omega)
  have hmp : m < p := Nat.lt_of_le_of_ne (Nat.le_of_dvd (by omega) hm) (fun h => hne (Or.inr h))
  have hsub : T ⊂ (Finset.range p).erase 0 := by
    refine Finset.ssubset_iff_of_subset (fun r hr => ?_) |>.mpr ⟨m, ?_, ?_⟩
    · simp only [T, Finset.mem_filter, Finset.mem_range] at hr
      refine Finset.mem_erase.mpr ⟨fun h0 => ?_, Finset.mem_range.mpr hr.1⟩
      rw [h0, Nat.Coprime, Nat.gcd_zero_left] at hr; omega
    · exact Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr hmp⟩
    · simp only [T, Finset.mem_filter, Finset.mem_range, not_and]
      intro _ hc
      have : Nat.gcd m p = m := Nat.gcd_eq_left hm
      rw [Nat.Coprime, this] at hc
      exact hne (Or.inl hc)
  have := Finset.card_lt_card hsub
  rw [Finset.card_erase_of_mem (Finset.mem_range.mpr (by omega)), Finset.card_range] at this
  omega

/-- Lucas's test, with the prime factors of `p - 1` listed (with multiplicity)
and every power computed by `powMod` with `n`-bit exponents. -/
theorem prime_of_cert (p a n : Nat) (fs : List Nat) (hp : 2 ≤ p) (hn : p - 1 < 2 ^ n)
    (hfs : ∀ f ∈ fs, f.Prime) (hprod : fs.prod = p - 1)
    (ha : powMod p n a (p - 1) = 1)
    (hq : ∀ f ∈ fs, powMod p n a ((p - 1) / f) ≠ 1) : p.Prime := by
  refine lucas hp (by rw [← powMod_eq p (by omega) n a _ hn]; exact ha) fun q hq' hd => ?_
  have hm := prime_of_dvd_prod hq' hfs (hprod ▸ hd)
  rw [← powMod_eq p (by omega) n a _ (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hn)]
  exact hq q hm

/-- Whether `p < 2^16` has no divisor `d` with `2 ≤ d` and `d² ≤ p`. -/
def smallPrime (p : Nat) : Bool :=
  2 ≤ p && p < 65536 && (List.range 256).all fun d => d < 2 || p < d * d || p % d != 0

/-- A prime below `2^16`, by trial division. -/
theorem prime_small (p : Nat) (h : smallPrime p = true) : p.Prime := by
  simp only [smallPrime, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨hp, hl⟩, hd⟩ := h
  refine Classical.byContradiction fun hnp => ?_
  have hm := Nat.minFac_prime (show p ≠ 1 by omega)
  have hsq := Nat.minFac_sq_le_self (by omega) hnp
  rw [Nat.pow_two] at hsq
  have h2 := hm.two_le
  have hlt : p.minFac < 256 := by
    refine Nat.lt_of_not_le fun h => ?_
    have := Nat.mul_le_mul h h
    omega
  have hmod : p % p.minFac = 0 := Nat.mod_eq_zero_of_dvd (Nat.minFac_dvd p)
  have := hd _ hlt
  omega

end VG.Proof.Pratt
