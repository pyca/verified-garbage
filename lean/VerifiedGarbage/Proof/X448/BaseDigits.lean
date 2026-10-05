import VerifiedGarbage.Impl.X448.BaseTable
import VerifiedGarbage.Proof.Ed448.Group.Projective
import Mathlib.Algebra.Module.NatInt

/- Proofs formerly in `VerifiedGarbage.Proof.X448.BaseTable`. -/
section

/-!
# The fixed-base tables represent `[k 256^j] B`, and `baseG` represents `[G] B`

`checkTables` walks the tables once (as `Proof/Ed25519/CombDigits.lean` does
Ed25519's): within table `j`, each entry is the previous one plus the first,
with the specification's `pointAdd`, compared projectively; the first entry of
table `j + 1` is `[256]` of table `j`'s, with the specification's `pointMul`.
The kernel evaluates it (`tables_check`).
-/

namespace VG.Proof.X448

open VG.Spec.Ed448 VG.Impl.X448 VG.Proof.Ed448 VG.Proof.EdwardsLaw
open Spec.X448 (Fe)

/-- The projective point `(x, y, 1)`. -/
def basePt (q : Fe × Fe) : Point := ⟨q.1, q.2, 1⟩

theorem basePt_rep {p : Point} {a : EPoint dZ} (h : Rep p a) {q : Fe × Fe}
    (hx : q.1 * p.Z = p.X) (hy : q.2 * p.Z = p.Y) : Rep (basePt q) a := by
  refine h.of_proj (show Ed448.toZ 1 ≠ 0 by rw [toZ_one]; exact one_ne_zero) ?_ ?_
  · show Ed448.toZ q.1 * Ed448.toZ p.Z = Ed448.toZ p.X * Ed448.toZ 1
    rw [toZ_one, mul_one, ← toZ_mul, hx]
  · show Ed448.toZ q.2 * Ed448.toZ p.Z = Ed448.toZ p.Y * Ed448.toZ 1
    rw [toZ_one, mul_one, ← toZ_mul, hy]

/-- The entries `p`, `p + b`, `p + 2b`, …, each compared with `p`'s representative. -/
private def checkRow (b p : Point) : List (Fe × Fe) → Bool
  | [] => true
  | q :: qs => (q.1 * p.Z == p.X && q.2 * p.Z == p.Y && p.Z != 0) &&
      checkRow b (pointAdd (basePt q) b) qs

private theorem checkRow_ok (b p : Point) (c a : EPoint dZ) (hb : Rep b c) (h : Rep p a)
    (qs : List (Fe × Fe)) (hc : checkRow b p qs = true) (i : Nat) (hi : i < qs.length) :
    Rep (basePt (qs.getD i (0, 1))) (i • c + a) := by
  induction qs generalizing p a i with
  | nil => exact absurd hi (Nat.not_lt_zero _)
  | cons q qs ih =>
    simp only [checkRow, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hc
    obtain ⟨⟨⟨hx, hy⟩, _⟩, hrest⟩ := hc
    have hq : Rep (basePt q) a := basePt_rep h hx hy
    cases i with
    | zero => rw [List.getD_cons_zero, zero_nsmul, zero_add]; exact hq
    | succ i =>
      have := ih _ _ (pointAdd_rep hq hb) hrest i (by simp only [List.length_cons] at hi; omega)
      rw [List.getD_cons_succ, succ_nsmul, add_assoc, add_comm c a]
      exact this

/-- Each table checked from the representative `b` of its first entry. -/
private def checkTables (b : Point) : List (List (Fe × Fe)) → Bool
  | [] => true
  | row :: rows => checkRow b b row && checkTables (pointMul 256 b) rows

private theorem checkTables_ok (b : Point) (c : EPoint dZ) (hb : Rep b c)
    (rows : List (List (Fe × Fe))) (hc : checkTables b rows = true) (j : Nat) (hj : j < rows.length)
    (k : Nat) (hk : k < (rows.getD j []).length) :
    Rep (basePt ((rows.getD j []).getD k (0, 1))) ((k + 1) • ((256 ^ j) • c)) := by
  induction rows generalizing b c j with
  | nil => exact absurd hj (Nat.not_lt_zero _)
  | cons row rows ih =>
    simp only [checkTables, Bool.and_eq_true] at hc
    cases j with
    | zero =>
      rw [List.getD_cons_zero] at hk ⊢
      have := checkRow_ok b b c c hb hb row hc.1 k hk
      rw [pow_zero, one_nsmul, succ_nsmul]
      exact this
    | succ j =>
      rw [List.getD_cons_succ] at hk ⊢
      have := ih (pointMul 256 b) ((256 : Nat) • c) (pointMul_rep 256 hb) hc.2 j
        (by simp only [List.length_cons] at hj; omega) hk
      rw [smul_smul, smul_smul] at this
      rw [smul_smul, pow_succ, ← Nat.mul_assoc]
      exact this

private theorem tables_check : checkTables basePoint baseRows = true := by decide +kernel

private theorem tables_length :
    baseRows.length = 57 ∧ baseRows.all (fun row => row.length == 8) = true := by decide +kernel

/-- Entry `k ≤ 8` of table `j < 57` is `[k 256^j] B`, affine. -/
theorem baseTable_ok (j k : Nat) (hj : j < 57) (hk : k < 9) :
    Rep (basePt (baseTable j k)) ((k * 256 ^ j) • baseAff) := by
  cases k with
  | zero =>
    rw [Nat.zero_mul, zero_smul]
    exact identity_rep
  | succ k =>
    have hrow : (baseRows.getD j []) ∈ baseRows := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [tables_length.1]; exact hj)]
      exact List.getElem_mem _
    have hlen : (baseRows.getD j []).length = 8 :=
      beq_iff_eq.mp (List.all_eq_true.mp tables_length.2 _ hrow)
    have hr := checkTables_ok basePoint baseAff basePoint_rep _ tables_check j
      (by rw [tables_length.1]; exact hj) k (by rw [hlen]; omega)
    simp only [baseTable, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    rw [smul_smul] at hr
    exact hr

/-- The constant the digits are offset by: `8 Σ_{j < 56} 256^j`. -/
def baseGVal : Nat := 8 * ((256 ^ 56 - 1) / 255)

private def baseGCheck (p : Point) : Bool :=
  baseG.1 * p.Z == p.X && baseG.2 * p.Z == p.Y && p.Z != 0

private theorem baseG_check : baseGCheck (pointMul baseGVal basePoint) = true := by decide +kernel

theorem baseG_ok : Rep (basePt baseG) (baseGVal • baseAff) := by
  have hp := pointMul_rep baseGVal basePoint_rep
  have hc := baseG_check
  simp only [baseGCheck, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hc
  obtain ⟨⟨hx, hy⟩, _⟩ := hc
  exact basePt_rep hp hx hy

/-- The constant the digits of a comb of all 57 tables are offset by: `8 Σ_{j < 57} 256^j`. -/
def baseGVal57 : Nat := 8 * ((256 ^ 57 - 1) / 255)

private def baseG57Check (p : Point) : Bool :=
  baseG57.1 * p.Z == p.X && baseG57.2 * p.Z == p.Y && p.Z != 0

private theorem baseG57_check : baseG57Check (pointMul baseGVal57 basePoint) = true := by decide +kernel

theorem baseG57_ok : Rep (basePt baseG57) (baseGVal57 • baseAff) := by
  have hp := pointMul_rep baseGVal57 basePoint_rep
  have hc := baseG57_check
  simp only [baseG57Check, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hc
  obtain ⟨⟨hx, hy⟩, _⟩ := hc
  exact basePt_rep hp hx hy

end VG.Proof.X448

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.BaseDigits`. -/
section

/-!
# The fixed-base comb's digits and partial sums

As `Proof/Ed25519/CombDigits.lean` for Ed25519's comb, for `8n` bits (448 for
X448, 456 for Ed448). The scalar `S < 256^n` has `2n` nibbles `n_i`; the digits
are `d_i = n_i - 8`, from `-8` to `7`. Step `j < n` adds `d_{2j+1} 256^j` to one
accumulator and `d_{2j} 256^j` to another, both starting at `G = combG n`; 16
times the first plus the second is `S` (`comb_total`), since
`G = 8 Σ_{j < n} 256^j`.

A negative digit adds the negation `(-x, y)` of the table entry `|d|`
(`baseEntry_ok`).
-/

namespace VG.Proof.X448

open VG.Impl.X448 VG.Proof.Ed448 VG.Proof.EdwardsLaw
open Spec.X448 (Fe)

/-- Digit `i` of `S` in radix 16. -/
def nib (S i : Nat) : Nat := (S / 16 ^ i) % 16

/-- `Σ_{j < c} n_{2j+1} 256^j`. -/
def oddSum (S : Nat) : Nat → Nat
  | 0 => 0
  | c + 1 => oddSum S c + nib S (2 * c + 1) * 256 ^ c

/-- `Σ_{j < c} n_{2j} 256^j`. -/
def evenSum (S : Nat) : Nat → Nat
  | 0 => 0
  | c + 1 => evenSum S c + nib S (2 * c) * 256 ^ c

theorem pow_256 (n : Nat) : 256 ^ n = 16 ^ (2 * n) := by
  rw [Nat.pow_mul]

theorem comb_partial (S : Nat) : ∀ n, 16 * oddSum S n + evenSum S n = S % 256 ^ n
  | 0 => by simp [oddSum, evenSum, Nat.mod_one]
  | n + 1 => by
    have ih := comb_partial S n
    have hd : S / 16 ^ (2 * n + 1) = S / 16 ^ (2 * n) / 16 := by
      rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ]
    have hm : S % 256 ^ (n + 1) = S % 256 ^ n + 256 ^ n * (S / 256 ^ n % 256) := by
      rw [Nat.pow_succ, Nat.mod_mul]
    simp only [oddSum, evenSum, nib]
    rw [hm, ← ih, hd, pow_256]
    generalize S / 16 ^ (2 * n) = x
    generalize 16 ^ (2 * n) = y
    have : x % 256 = x % 16 + 16 * (x / 16 % 16) := by omega
    rw [this]; ring

/-- `Σ_{j < c} 256^j`. -/
def geom : Nat → Nat
  | 0 => 0
  | c + 1 => geom c + 256 ^ c

/-- The constant the digits of a comb of `n` tables are offset by: `8 Σ_{j < n} 256^j`. -/
def combG (n : Nat) : Nat := 8 * geom n

theorem combG_56 : combG 56 = baseGVal := by decide

theorem combG_57 : combG 57 = baseGVal57 := by decide

/-- The comb's digit `i`: `n_i - 8`, from `-8` to `7`. -/
def sdig (S i : Nat) : ℤ := (nib S i : ℤ) - 8

/-- `Σ_{j < c} d_{2j+1} 256^j`. -/
def oddSumZ (S : Nat) : Nat → ℤ
  | 0 => 0
  | c + 1 => oddSumZ S c + sdig S (2 * c + 1) * 256 ^ c

/-- `Σ_{j < c} d_{2j} 256^j`. -/
def evenSumZ (S : Nat) : Nat → ℤ
  | 0 => 0
  | c + 1 => evenSumZ S c + sdig S (2 * c) * 256 ^ c

theorem oddSumZ_eq (S : Nat) : ∀ c, oddSumZ S c = oddSum S c - 8 * geom c
  | 0 => rfl
  | c + 1 => by
    simp only [oddSumZ, oddSum, geom, oddSumZ_eq S c, sdig]
    push_cast; ring

theorem evenSumZ_eq (S : Nat) : ∀ c, evenSumZ S c = evenSum S c - 8 * geom c
  | 0 => rfl
  | c + 1 => by
    simp only [evenSumZ, evenSum, geom, evenSumZ_eq S c, sdig]
    push_cast; ring

/-- The two accumulators' multiples of `B` give the scalar: `16 (G + Σ_j d_{2j+1} 256^j) +
(G + Σ_j d_{2j} 256^j) = S`. -/
theorem comb_total {n S : Nat} (hS : S < 256 ^ n) :
    16 * ((combG n : ℤ) + oddSumZ S n) + (combG n + evenSumZ S n) = S := by
  simp only [oddSumZ_eq, evenSumZ_eq, combG]
  have h := comb_partial S n
  rw [Nat.mod_eq_of_lt hS] at h
  have h' : (16 * oddSum S n + evenSum S n : ℤ) = S := by exact_mod_cast h
  push_cast
  linear_combination h'

/-- A nibble from its four bits. -/
theorem nib_bits (S i : Nat) :
    nib S i = (((S / 2 ^ (4 * i + 3)) % 2 * 2 + (S / 2 ^ (4 * i + 2)) % 2) * 2 +
      (S / 2 ^ (4 * i + 1)) % 2) * 2 + (S / 2 ^ (4 * i)) % 2 := by
  have h16 : 16 ^ i = 2 ^ (4 * i) := by rw [Nat.pow_mul]
  have e : ∀ t, S / 2 ^ (4 * i + t) = S / 16 ^ i / 2 ^ t := fun t => by
    rw [h16, Nat.div_div_eq_div_mul, ← Nat.pow_add]
  rw [nib, e 3, e 2, e 1, ← Nat.add_zero (4 * i), e 0]
  simp only [Nat.pow_zero, Nat.div_one, Nat.reducePow]
  omega

theorem nib_lt (S i : Nat) : nib S i < 16 := Nat.mod_lt _ (by decide)

/-- The magnitude of the digit `n - 8`. -/
def mag (n : Nat) : Nat := if n < 8 then 8 - n else n - 8

theorem mag_lt {n : Nat} (hn : n < 16) : mag n < 9 := by unfold mag; split <;> omega

/-- The affine point `(x, y)` negated: `(-x, y)`. -/
def negAff (q : Fe × Fe) : Fe × Fe := (0 - q.1, q.2)

theorem basePt_neg (q : Fe × Fe) : basePt (negAff q) = negPoint (basePt q) := rfl

/-- The entry for the digit `n - 8` of table `j`, negated for a negative digit, represents
`[(n - 8) 256^j] B`. -/
theorem baseEntry_ok (j n : Nat) (hj : j < 57) (hn : n < 16) :
    Rep (basePt (if n < 8 then negAff (baseTable j (mag n)) else baseTable j (mag n)))
      ((((n : ℤ) - 8) * 256 ^ j) • baseAff) := by
  have hr := baseTable_ok j (mag n) hj (mag_lt hn)
  by_cases hlt : n < 8
  · simp only [hlt, ↓reduceIte, basePt_neg]
    have e : ((n : ℤ) - 8) * 256 ^ j = -(((mag n * 256 ^ j : Nat) : ℤ)) := by
      simp only [mag, hlt, ↓reduceIte]; push_cast [Nat.cast_sub (by omega : n ≤ 8)]; ring
    rw [e, neg_smul, natCast_zsmul]
    exact hr.neg
  · simp only [hlt, ↓reduceIte]
    have e : ((n : ℤ) - 8) * 256 ^ j = (((mag n * 256 ^ j : Nat) : ℤ)) := by
      simp only [mag, hlt, ↓reduceIte]; push_cast [Nat.cast_sub (by omega : 8 ≤ n)]; ring
    rw [e, natCast_zsmul]
    exact hr

theorem zsmul_16 (v w : ℤ) (P : EPoint dZ) :
    (16 : Nat) • (v • P) + w • P = (16 * v + w) • P := by
  rw [add_smul, mul_smul, ← natCast_zsmul]; rfl

end VG.Proof.X448

end
