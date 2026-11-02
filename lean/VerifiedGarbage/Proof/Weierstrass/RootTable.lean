module

public import VerifiedGarbage.Impl.EcKey.Compressed.RootTable
public import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Weierstrass.Sqrt
import VerifiedGarbage.Proof.Weierstrass.RootPowers

/-!
# Correctness of the square root by a table (`rootTable`)

For `p - 1 = q 16ⁿ` (`q` odd), `c` with `c^(2^(4n-1)) = -1` and the table
`T m d = c^(d 16^m)` whose last row has 16 different entries, `rootTable`
gives a root of every square (`rootTable_square`). Every root of unity of
order dividing `2^(k+1)` is a power of an `h` with `h^(2^k) = -1`
(`pow_cyc`), from the curve law's fact that two square roots differ only by
sign. So, with `z = t c^k` for the number `k` of the digits found so far,
`z^(16^(n-j)) = 1` after `j` digits (`kGo_inv`): digit `j`'s `y` is
`z^(16^(n-1-j))`, a 16th root of unity, so a power `g^e` of
`g = c^(16^(n-1))` (an entry of the last row), and the digit
`(16 - e) mod 16` makes the next `z`'s power one. After the `n` digits,
`t c^k = 1`; for a square, `t = c^(2m)` (`pow_cyc` again, for `y^q`), so `k`
is even, and `(r c^(k/2))² = a t c^k = a`.
-/

-- separate module: shared by any curve's table root, apart from each curve's and target's proofs

@[expose] public section

namespace VG.Proof.Weierstrass

open Spec.Weierstrass VG.Impl.EcKey.Compressed

variable {C : Curve}

theorem two_mul_two_pow (k : Nat) : 2 * 2 ^ k = 2 ^ (k + 1) := by rw [Nat.pow_succ, Nat.mul_comm]

/-- Every `2^(k+1)`-th root of unity is a power of `h`, for `h^(2^k) = -1`. -/
theorem pow_cyc (hL : Law C) : ∀ (k : Nat) (h x : Fe C), h ^ (2 ^ k) = -1 → x ^ (2 ^ (k + 1)) = 1 →
    ∃ e < 2 ^ (k + 1), x = h ^ e
  | 0, h, x, hh, hx => by
    rw [Nat.pow_zero, Lean.Grind.Semiring.pow_one] at hh
    have hx' : x * x = 1 * 1 := by
      rw [← Lean.Grind.Semiring.pow_two, Lean.Grind.Semiring.mul_one]; exact hx
    rcases square_roots_eq_or_neg hL hx' with h1 | h1
    · exact ⟨0, by decide, by rw [h1, Lean.Grind.Semiring.pow_zero]⟩
    · exact ⟨1, by decide, by rw [h1, Lean.Grind.Semiring.pow_one, hh]⟩
  | k + 1, h, x, hh, hx => by
    have hh' : (h * h) ^ (2 ^ k) = -1 := by
      rw [← Lean.Grind.Semiring.pow_two, pow_mul_exponents, two_mul_two_pow]; exact hh
    have hx' : (x * x) ^ (2 ^ (k + 1)) = 1 := by
      rw [← Lean.Grind.Semiring.pow_two, pow_mul_exponents, two_mul_two_pow]; exact hx
    obtain ⟨e, he, hxe⟩ := pow_cyc hL k (h * h) (x * x) hh' hx'
    have hsq : x * x = h ^ e * h ^ e := by rw [hxe, mul_pow_exponent]
    have h2 := two_mul_two_pow (k + 1)
    rcases square_roots_eq_or_neg hL hsq with h1 | h1
    · exact ⟨e, by omega, h1⟩
    · refine ⟨e + 2 ^ (k + 1), by omega, ?_⟩
      rw [h1, Lean.Grind.Semiring.pow_add, hh]
      grind

/-- The table's product: `y c^((k mod 16^j) 16^o)`. -/
theorem tacc_pow {T : Nat → Nat → Fe C} {c : Fe C} (hT : ∀ m d, T m d = c ^ (d * 16 ^ m)) (o k : Nat)
    (y : Fe C) : ∀ j, tacc T o k y j = y * c ^ (k % 16 ^ j * 16 ^ o)
  | 0 => by
    rw [tacc, Nat.pow_zero, Nat.mod_one, Nat.zero_mul, Lean.Grind.Semiring.pow_zero, Lean.Grind.Semiring.mul_one]
  | j + 1 => by
    rw [tacc, tacc_pow hT o k y j, hT, Lean.Grind.Semiring.mul_assoc, ← Lean.Grind.Semiring.pow_add]
    refine congrArg (fun e => y * c ^ e) ?_
    rw [Nat.mod_pow_succ, Nat.pow_add]
    grind

/-- `digAcc` of an entry, for a row of different entries. -/
theorem digAcc_eq {G : Nat → Fe C} (hG : ∀ e e', e < 16 → e' < 16 → G e = G e' → e = e') {e : Nat}
    (he : e < 16) : ∀ f, f ≤ 16 → digAcc G (G e) f = if e < f then (16 - e) % 16 else 0
  | 0, _ => by rw [digAcc, ite_eq_right (by omega)]
  | f + 1, hf => by
    rw [digAcc, digAcc_eq hG he f (by omega)]
    by_cases h : e = f
    · subst h
      rw [ite_eq_right (Nat.lt_irrefl e), ite_eq_left rfl, ite_eq_left (Nat.lt_succ_self e), Nat.zero_add]
    · have hne : G e ≠ G f := fun h' => h (hG e f he (by omega) h')
      rw [ite_eq_right hne, Nat.add_zero]
      by_cases hl : e < f
      · rw [ite_eq_left hl, ite_eq_left (by omega)]
      · rw [ite_eq_right hl, ite_eq_right (by omega)]

theorem neg_one_ne_one (hp3 : 2 < C.p) : (-1 : Fe C) ≠ 1 := by
  intro h
  have h' := congrArg Fin.val h
  have h1 : ((1 : Fe C) : Nat) = 1 := by show 1 % C.p = 1; exact Nat.mod_eq_of_lt (by omega)
  rw [Fin.val_neg', h1, Nat.mod_eq_of_lt (by omega)] at h'
  omega

theorem one_pow' (l : Nat) : (1 : Fe C) ^ l = 1 := by
  induction l with
  | zero => rw [Lean.Grind.Semiring.pow_zero]
  | succ l ih => rw [Lean.Grind.Semiring.pow_succ, ih, Lean.Grind.Semiring.mul_one]

theorem neg_one_pow_two : ((-1 : Fe C)) ^ 2 = 1 := by
  rw [Lean.Grind.Semiring.pow_two]; grind

theorem neg_one_pow_odd (l : Nat) : (-1 : Fe C) ^ (2 * l + 1) = -1 := by
  rw [Lean.Grind.Semiring.pow_succ, ← pow_mul_exponents, neg_one_pow_two, one_pow',
    Lean.Grind.Semiring.one_mul]

/-- `16^(n-1) 8 = 2^(4n-1)`. -/
theorem sixteen_pow_mul_eight {n : Nat} (hn : 0 < n) : 16 ^ (n - 1) * 2 ^ 3 = 2 ^ (4 * n - 1) := by
  rw [show (16 : Nat) = 2 ^ 4 from rfl, ← Nat.pow_mul, ← Nat.pow_add]
  congr 1
  omega

theorem sixteen_pow {n : Nat} : 16 ^ n = 2 ^ (4 * n) := by
  rw [show (16 : Nat) = 2 ^ 4 from rfl, ← Nat.pow_mul]

/-- The number of `j` digits is below `16^j`. -/
theorem kGo_lt {p : Nat} [NeZero p] (T : Nat → Nat → Fin p) (s : Nat → Fin p) (n : Nat) :
    ∀ j, kGo T s n j < 16 ^ j
  | 0 => by rw [kGo]; decide
  | j + 1 => by
    rw [kGo]
    have h := kGo_lt T s n j
    have hd : digAcc (T (n - 1)) (tacc T (n - 1 - j) (kGo T s n j) (s (n - 1 - j)) j) 16 % 16 ≤ 15 := by omega
    have := Nat.mul_le_mul_right (16 ^ j) hd
    rw [Nat.pow_succ]; omega

/-- The digits found keep `(t c^k)^(16^(n-j)) = 1`. -/
theorem kGo_inv (hL : Law C) {c t : Fe C} {T : Nat → Nat → Fe C} {s : Nat → Fe C} {n : Nat} (hn : 0 < n)
    (hc : c ^ (2 ^ (4 * n - 1)) = -1) (hT : ∀ m d, T m d = c ^ (d * 16 ^ m))
    (hG : ∀ e e', e < 16 → e' < 16 → T (n - 1) e = T (n - 1) e' → e = e')
    (hs : ∀ m, s m = t ^ (16 ^ m)) (ht : t ^ (16 ^ n) = 1) :
    ∀ j, j ≤ n → kGo T s n j < 16 ^ j ∧ (t * c ^ kGo T s n j) ^ (16 ^ (n - j)) = 1
  | 0, _ => by
    refine ⟨by rw [kGo]; decide, ?_⟩
    rw [kGo, Lean.Grind.Semiring.pow_zero, Lean.Grind.Semiring.mul_one, Nat.sub_zero]; exact ht
  | j + 1, hj => by
    obtain ⟨hk, hz⟩ := kGo_inv hL hn hc hT hG hs ht j (by omega)
    generalize hK : kGo T s n j = k at hk hz
    have hkGo : kGo T s n (j + 1) =
        k + digAcc (T (n - 1)) (tacc T (n - 1 - j) k (s (n - 1 - j)) j) 16 % 16 * 16 ^ j := by
      rw [kGo, hK]
    generalize ho : n - 1 - j = o at hkGo
    have hno : n - j = o + 1 := by omega
    -- `y = z^(16^o)`.
    have hy : tacc T o k (s o) j = (t * c ^ k) ^ (16 ^ o) := by
      rw [tacc_pow hT, hs, Nat.mod_eq_of_lt hk, mul_pow_exponent, pow_mul_exponents]
    have hy16 : (tacc T o k (s o) j) ^ (2 ^ 4) = 1 := by
      rw [hy, pow_mul_exponents, ← hz, hno, Nat.pow_succ 16 o]
    have hg : (c ^ (16 ^ (n - 1))) ^ (2 ^ 3) = -1 := by
      rw [pow_mul_exponents, sixteen_pow_mul_eight hn]; exact hc
    obtain ⟨e, he, hye⟩ := pow_cyc hL 3 _ _ hg hy16
    have hTe : T (n - 1) e = (c ^ (16 ^ (n - 1))) ^ e := by rw [hT, pow_mul_exponents, Nat.mul_comm]
    have hd : digAcc (T (n - 1)) (tacc T o k (s o) j) 16 % 16 = (16 - e) % 16 := by
      rw [hye, ← hTe, digAcc_eq hG he 16 (Nat.le_refl _), ite_eq_left he, Nat.mod_mod]
    rw [hd] at hkGo
    rw [hkGo]
    have hdl : (16 - e) % 16 ≤ 15 := by omega
    refine ⟨?_, ?_⟩
    · have := Nat.mul_le_mul_right (16 ^ j) hdl
      rw [Nat.pow_succ]; omega
    · generalize hgd : c ^ (16 ^ (n - 1)) = g at hg hTe hye
      have hcd : (c ^ ((16 - e) % 16 * 16 ^ j)) ^ (16 ^ o) = g ^ ((16 - e) % 16) := by
        rw [← hgd, pow_mul_exponents, pow_mul_exponents, Nat.mul_assoc, ← Nat.pow_add,
          show j + o = n - 1 by omega, Nat.mul_comm]
      rw [show n - (j + 1) = o by omega, Lean.Grind.Semiring.pow_add, ← Lean.Grind.Semiring.mul_assoc,
        mul_pow_exponent, ← hy, hye, hcd, ← Lean.Grind.Semiring.pow_add]
      by_cases he0 : e = 0
      · subst he0
        rw [show 0 + (16 - 0) % 16 = 0 from rfl, Lean.Grind.Semiring.pow_zero]
      · rw [show e + (16 - e) % 16 = 2 ^ 3 * 2 by omega, ← pow_mul_exponents, hg, neg_one_pow_two]

/-- The candidate root of a square is a root. -/
theorem rootTable_square (hL : Law C) (hp3 : 2 < C.p) {q n : Nat} {c : Fe C} {T : Nat → Nat → Fe C}
    (hn : 0 < n) (hq : q % 2 = 1) (hp : C.p - 1 = q * 16 ^ n) (hc : c ^ (2 ^ (4 * n - 1)) = -1)
    (hT : ∀ m d, T m d = c ^ (d * 16 ^ m))
    (hG : ∀ e e', e < 16 → e' < 16 → T (n - 1) e = T (n - 1) e' → e = e')
    (a : Fe C) (ha : ∃ y : Fe C, y * y = a) : rootTable a q n T * rootTable a q n T = a := by
  unfold rootTable
  simp only []
  rw [pow_eq_npow]
  generalize hw : a ^ ((q - 1) / 2) = w
  generalize hK : kGo T (fun m => pow (w * (w * a)) (16 ^ m)) n n = K
  rw [tacc_pow hT, Nat.pow_zero, Nat.mul_one]
  by_cases ha0 : a = 0
  · subst ha0; grind
  obtain ⟨y, hy⟩ := ha
  have hy0 : y ≠ 0 := by intro h; apply ha0; rw [← hy, h]; grind
  -- `t = a^q`, `t^(16^n) = 1`.
  have ht : w * (w * a) = a ^ q := by
    rw [← hw, ← Lean.Grind.Semiring.mul_assoc, ← Lean.Grind.Semiring.pow_add, ← Lean.Grind.Semiring.pow_succ]
    exact congrArg (a ^ ·) (by omega)
  have ht1 : (w * (w * a)) ^ (16 ^ n) = 1 := by
    rw [ht, pow_mul_exponents, ← hp]; exact root_fermat hL hp3 a ha0
  obtain ⟨hKl, hKz⟩ := kGo_inv hL hn hc hT hG (fun m => pow_eq_npow _ _) ht1 n (Nat.le_refl _)
  rw [hK, Nat.sub_self, Nat.pow_zero, Lean.Grind.Semiring.pow_one] at hKz
  rw [hK] at hKl
  -- `K` is even.
  have hu : (y ^ q) ^ (2 ^ (4 * n - 1 + 1)) = 1 := by
    rw [pow_mul_exponents, show 4 * n - 1 + 1 = 4 * n by omega, ← sixteen_pow, ← hp]
    exact root_fermat hL hp3 y hy0
  obtain ⟨m, -, hm⟩ := pow_cyc hL (4 * n - 1) c (y ^ q) hc hu
  have hKe : K % 2 = 0 := by
    rcases Nat.mod_two_eq_zero_or_one K with h0 | hodd
    · exact h0
    exfalso
    have hta : w * (w * a) = c ^ m * c ^ m := by rw [ht, ← hy, mul_pow_exponent, hm]
    have h1 : c ^ (2 * m + K) = 1 := by
      rw [Lean.Grind.Semiring.pow_add, show 2 * m = m + m by omega, Lean.Grind.Semiring.pow_add, ← hta]
      exact hKz
    have h2 : (c ^ (2 * m + K)) ^ (2 ^ (4 * n - 1)) = -1 := by
      rw [pow_mul_exponents, Nat.mul_comm, ← pow_mul_exponents, hc,
        show 2 * m + K = 2 * (m + K / 2) + 1 by omega, neg_one_pow_odd]
    rw [h1, one_pow'] at h2
    exact neg_one_ne_one hp3 h2.symm
  rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hKl)]
  have hr : w * a * (w * a) = a * (w * (w * a)) := by grind
  calc w * a * c ^ (K / 2) * (w * a * c ^ (K / 2)) = a * (w * (w * a) * c ^ (K / 2 + K / 2)) := by
        rw [Lean.Grind.Semiring.pow_add]; grind
    _ = a := by rw [show K / 2 + K / 2 = K by omega, hKz, Lean.Grind.Semiring.mul_one]

end VG.Proof.Weierstrass
