module
public import VerifiedGarbage.Proof.X25519.Limbs
public import VerifiedGarbage.Spec.X448

/-!
# X448: numbers of 32-bit limbs

The arithmetic of the 32-bit-limb implementations (`Impl/X448/PPC64LE.lean`,
`Impl/X448/RISCV64.lean`) on natural numbers, with X25519's
numbers of limbs (`val32`) and carries (`chain`, `out`): a row of a product,
the fold of a product's top half (`2⁴⁴⁸ ≡ 2²²⁴ + 1`), the carry out folded in
twice (`tail`), `4p` as limbs, and the final reduction.
-/

@[expose] public section

namespace VG.Proof.X448.Limbs32

open VG.Proof.X25519
open VG.Spec.X448 (P)

/-! `2⁴⁴⁸` is written `2²²⁴ · 2²²⁴` throughout: Lean evaluates powers of
numerals only up to `2²⁵⁶`, and `omega` multiplies the two. -/

theorem pow448 : (2 : Nat) ^ (32 * 14) = 2 ^ 224 * 2 ^ 224 := by decide +kernel

theorem pow448_eq : 2 ^ 224 * 2 ^ 224 = P + (2 ^ 224 + 1) := by decide +kernel

theorem P_eq : P = 2 ^ 224 * 2 ^ 224 - 2 ^ 224 - 1 := by decide +kernel

/-- `2⁴⁴⁸ ≡ 2²²⁴ + 1` modulo `p`. -/
theorem fold448 (lo hi : Nat) : (lo + 2 ^ 224 * 2 ^ 224 * hi) % P = (lo + (2 ^ 224 + 1) * hi) % P := by
  rw [pow448_eq, Nat.add_mul, Nat.add_comm (P * hi), ← Nat.add_assoc, Nat.add_mul_mod_self_left]

/-! ## A row of a product -/

/-- The limbs after row `i`: those below `i`, the row's limbs, and its carry. -/
def rowAcc (acc a b : Nat → Nat) (i k : Nat) : Nat :=
  if k < i then acc k else if k < i + 14 then out (rowC acc a b i) 0 (k - i)
  else chain (rowC acc a b i) 0 14

theorem row_val {acc a b : Nat → Nat} {i : Nat} (hv : val32 acc (i + 14) = val32 a i * val32 b 14) :
    val32 (rowAcc acc a b i) (i + 15) = val32 a (i + 1) * val32 b 14 := by
  have e1 : val32 (rowAcc acc a b i) i = val32 acc i :=
    val32_congr fun k hk => by simp [rowAcc, hk]
  have e2 : val32 (fun k => rowAcc acc a b i (i + k)) 15 =
      val32 (out (rowC acc a b i) 0) 14 + 2 ^ 224 * 2 ^ 224 * chain (rowC acc a b i) 0 14 := by
    rw [val32_succ, val32_congr (g := out (rowC acc a b i) 0) fun k hk => by
      simp only [rowAcc, show ¬ i + k < i by omega, show i + k < i + 14 by omega, ite_false, ite_true,
        Nat.add_sub_cancel_left]]
    simp only [rowAcc, show ¬ i + 14 < i by omega, Nat.lt_irrefl, ite_false]
    rw [pow448]
  have e3 : val32 (rowC acc a b i) 14 = a i * val32 b 14 + val32 (fun k => acc (i + k)) 14 := by
    rw [← val32_cmul, ← val32_add]; rfl
  have hc := chain_val (rowC acc a b i) 0 14
  rw [pow448, Nat.add_zero, e3] at hc
  rw [val32_append _ i 15, e1, e2, hc, val32_succ a i, Nat.add_mul, ← hv, val32_append acc i 14,
    Nat.mul_add, Nat.mul_assoc]
  omega

theorem rowAcc_lt {acc a b : Nat → Nat} {i : Nat} (hacc : ∀ k < i, acc k < 2 ^ 32)
    (hc : ∀ j < 14, rowC acc a b i j + 2 ^ 32 ≤ 2 ^ 64) :
    ∀ k < i + 15, rowAcc acc a b i k < 2 ^ 32 := by
  intro k _
  simp only [rowAcc]
  split
  · exact hacc k (by omega)
  · split
    · exact out_lt _ _ _
    · exact chain_lt hc (by decide) 14 (Nat.le_refl _)

/-! ## The fold of a product -/

/-- The sums of the limbs of `lo + hi + 2²²⁴ hi`, with the upper half of
`2²²⁴ hi` folded once more: `lo_k + hi_k + hi_{k+7}` below 7, and
`lo_k + 2 hi_k + hi_{k-7}` from 7. -/
def foldC (acc : Nat → Nat) (k : Nat) : Nat :=
  if k < 7 then acc k + acc (14 + k) + acc (14 + (k + 7))
  else acc k + acc (14 + k) + acc (14 + k) + acc (14 + (k - 7))

theorem foldC_le {acc : Nat → Nat} (h : ∀ k < 28, acc k < 2 ^ 32) :
    ∀ k < 14, foldC acc k + 2 ^ 32 ≤ 2 ^ 64 := by
  intro k hk
  have := h k (by omega)
  have := h (14 + k) (by omega)
  simp only [foldC]
  split
  · have := h (14 + (k + 7)) (by omega); omega
  · have := h (14 + (k - 7)) (by omega); omega

theorem foldC_facts {acc : Nat → Nat} (h : ∀ k < 28, acc k < 2 ^ 32) :
    val32 (foldC acc) 14 < 5 * 2 ^ 224 * 2 ^ 224 ∧ val32 (foldC acc) 14 % P = val32 acc 28 % P := by
  -- The two halves of the product, and the two halves of its top half.
  let L := val32 acc 14
  let H := val32 (fun k => acc (14 + k)) 14
  let Hl := val32 (fun k => acc (14 + k)) 7
  let Hh := val32 (fun k => acc (21 + k)) 7
  have hL : L < 2 ^ 224 * 2 ^ 224 := by
    have := val32_lt (f := acc) (n := 14) fun k hk => h k (by omega); rwa [pow448] at this
  have hH : H < 2 ^ 224 * 2 ^ 224 := by
    have := val32_lt (f := fun k => acc (14 + k)) (n := 14) fun k hk => h (14 + k) (by omega)
    rwa [pow448] at this
  have hHl : Hl < 2 ^ 224 := val32_lt fun k hk => h (14 + k) (by omega)
  have hHh : Hh < 2 ^ 224 := val32_lt fun k hk => h (21 + k) (by omega)
  have eH : H = Hl + 2 ^ 224 * Hh := by
    show val32 _ (7 + 7) = _
    rw [val32_append]
    exact congrArg (Hl + 2 ^ 224 * ·) (val32_congr fun k _ => congrArg acc (by omega))
  have eA : val32 acc 28 = L + 2 ^ 224 * 2 ^ 224 * H := by
    have := val32_append acc 14 14; rwa [pow448] at this
  -- The sums, as the low and high parts of the fold.
  let g : Nat → Nat := fun k => if k < 7 then acc (14 + (k + 7)) else acc (14 + k) + acc (14 + (k - 7))
  have eF : val32 (foldC acc) 14 = L + H + val32 g 14 := by
    rw [← val32_add, ← val32_add]
    exact val32_congr fun k _ => by simp only [foldC, g]; split <;> omega
  have eG : val32 g 14 = Hh + 2 ^ 224 * (Hh + Hl) := by
    show val32 g (7 + 7) = _
    have a : val32 g 7 = Hh := val32_congr fun k hk => by
      simp only [g, hk, ite_true]; exact congrArg acc (by omega)
    have c : val32 (fun k => g (7 + k)) 7 = Hh + Hl := by
      rw [← val32_add]
      exact val32_congr fun k _ => by
        simp only [g, show ¬ 7 + k < 7 by omega, ite_false]
        rw [show 14 + (7 + k) = 21 + k by omega, show 14 + (7 + k - 7) = 14 + k by omega]
    rw [val32_append, a, c]
  rw [eF, eG]
  refine ⟨by omega, ?_⟩
  rw [eA, fold448, show L + (2 ^ 224 + 1) * H = L + Hl + 2 ^ 224 * Hl + 2 ^ 224 * Hh + 2 ^ 224 * 2 ^ 224 * Hh by
      rw [eH]; omega, fold448]
  congr 1
  omega

/-! ## The carry out folded in -/

/-- The sums of a fold: the limbs `l`, and the carry `c` into limb 7 (and
into limb 0, as the carry in). -/
def foldL (l : Nat → Nat) (c k : Nat) : Nat := l k + if k = 7 then c else 0

theorem val32_foldL (l : Nat → Nat) (c : Nat) : val32 (foldL l c) 14 = val32 l 14 + 2 ^ 224 * c := by
  rw [show foldL l c = fun k => l k + (if k = 7 then c else 0) from rfl, val32_add]
  congr 1
  have e : ∀ n, val32 (fun k => if k = 7 then c else 0) (8 + n) = 2 ^ 224 * c := by
    intro n
    rw [val32_append, val32_congr (g := fun _ => 0) (n := n) (fun k _ => by
        simp only [show 8 + k ≠ 7 by omega, ite_false]), val32_zero_fn, Nat.mul_zero, Nat.add_zero,
      val32_succ, val32_congr (g := fun _ => 0) (n := 7) (fun k hk => by
        simp only [show k ≠ 7 by omega, ite_false]), val32_zero_fn]
    simp
  exact e 6

/-- The limbs of a fold of the carry `c` into the limbs `l`. -/
def fold1 (l : Nat → Nat) (c : Nat) : Nat → Nat := out (foldL l c) c

/-- Its carry out. -/
def fold1C (l : Nat → Nat) (c : Nat) : Nat := chain (foldL l c) c 14

theorem fold1_facts {l : Nat → Nat} (hl : ∀ k < 14, l k < 2 ^ 32) {c : Nat} (hc : c < 2 ^ 32) :
    (∀ k < 14, foldL l c k + 2 ^ 32 ≤ 2 ^ 64) ∧ (∀ k < 14, fold1 l c k < 2 ^ 32) ∧
      val32 (fold1 l c) 14 + 2 ^ 224 * 2 ^ 224 * fold1C l c = val32 l 14 + (2 ^ 224 + 1) * c := by
  refine ⟨fun k hk => ?_, fun k _ => out_lt _ _ _, ?_⟩
  · have := hl k hk; simp only [foldL]; split <;> omega
  · have hv := chain_val (foldL l c) c 14
    rw [val32_foldL, pow448] at hv
    simp only [fold1, fold1C]
    omega

theorem chain_congr {c c' : Nat → Nat} {cin n : Nat} (h : ∀ j < n, c j = c' j) :
    ∀ k ≤ n, chain c cin k = chain c' cin k
  | 0, _ => rfl
  | k + 1, hk => by rw [chain_succ, chain_succ, h k (by omega), chain_congr h k (by omega)]

/-- A fold reads only the 14 limbs. -/
theorem fold1_congr {l l' : Nat → Nat} (h : ∀ j < 14, l j = l' j) (c : Nat) :
    (∀ k < 14, fold1 l c k = fold1 l' c k) ∧ fold1C l c = fold1C l' c := by
  have e : ∀ j < 14, foldL l c j = foldL l' c j := fun j hj => by simp only [foldL, h j hj]
  refine ⟨fun k hk => ?_, chain_congr e 14 (Nat.le_refl _)⟩
  simp only [fold1, out]
  rw [e k hk, chain_congr e k (by omega)]

/-- The limbs after `tail`: the carry `c` folded in twice. -/
def tailL (l : Nat → Nat) (c : Nat) : Nat → Nat := fold1 (fold1 l c) (fold1C l c)

theorem tail_facts {l : Nat → Nat} (hl : ∀ k < 14, l k < 2 ^ 32) {c : Nat} (hc : c ≤ 4) :
    fold1C l c ≤ 1 ∧ fold1C (fold1 l c) (fold1C l c) = 0 ∧
      val32 (tailL l c) 14 % P = (val32 l 14 + 2 ^ 224 * 2 ^ 224 * c) % P := by
  obtain ⟨-, h1l, h1v⟩ := fold1_facts hl (c := c) (by omega)
  have hL := val32_lt (f := l) (n := 14) hl
  have hL1 := val32_lt (f := fold1 l c) (n := 14) h1l
  rw [pow448] at hL hL1
  have ht : fold1C l c ≤ 1 := by omega
  obtain ⟨-, -, h2v⟩ := fold1_facts h1l (c := fold1C l c) (by omega)
  have ht2 : fold1C (fold1 l c) (fold1C l c) = 0 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ht with h0 | h1
    · rw [h0] at h2v ⊢; rw [h0] at h1v; omega
    · rw [h1] at h1v h2v ⊢; omega
  refine ⟨ht, ht2, ?_⟩
  rw [ht2, Nat.mul_zero, Nat.add_zero] at h2v
  rw [tailL, h2v, ← fold448, h1v, ← fold448]

/-! ## Sums and differences -/

/-- Limb `k` of `4p`. -/
def fourP (k : Nat) : Nat := if k = 7 then 2 ^ 34 - 8 else 2 ^ 34 - 4

theorem val32_fourP : val32 fourP 14 = 4 * P := by decide +kernel

/-- The sums of a difference: `a_k + 4p_k - b_k`. -/
def subC (a b : Nat → Nat) (k : Nat) : Nat := a k + fourP k - b k

theorem subC_facts {a b : Nat → Nat} (ha : ∀ k < 14, a k < 2 ^ 32) (hb : ∀ k < 14, b k < 2 ^ 32) :
    (∀ k < 14, subC a b k + 2 ^ 32 ≤ 2 ^ 64) ∧ val32 (subC a b) 14 + val32 b 14 = val32 a 14 + 4 * P := by
  have hK : ∀ k, 2 ^ 34 - 8 ≤ fourP k ∧ fourP k ≤ 2 ^ 34 := fun k => by
    simp only [fourP]; split <;> omega
  refine ⟨fun k hk => ?_, ?_⟩
  · have := ha k hk; have := hb k hk; have := hK k
    simp only [subC]; omega
  · rw [← val32_add, ← val32_fourP, ← val32_add]
    exact val32_congr fun k hk => by have := hK k; have := hb k hk; simp only [subC]; omega

/-- The carry out of the limbs of a sum, difference or folded product of
numbers below `2⁴⁴⁸` is at most 4. -/
theorem carry_le {c : Nat → Nat} (h : val32 c 14 < 5 * 2 ^ 224 * 2 ^ 224) : chain c 0 14 ≤ 4 := by
  have hv := chain_val c 0 14
  rw [pow448] at hv
  omega

/-! ## The final reduction -/

/-- The limbs of `x mod p`: those of `x`, or those of `x + 2²²⁴ + 1` if it
carries out. -/
def frR (l : Nat → Nat) (k : Nat) : Nat := sel (fold1C l 1) (l k) (fold1 l 1 k)

theorem freeze_facts {l : Nat → Nat} (hl : ∀ k < 14, l k < 2 ^ 32) :
    fold1C l 1 ≤ 1 ∧ (∀ k < 14, frR l k < 2 ^ 32) ∧ val32 (frR l) 14 = val32 l 14 % P := by
  obtain ⟨-, h1l, h1v⟩ := fold1_facts hl (c := 1) (by decide)
  have hL := val32_lt (f := l) (n := 14) hl
  have hL1 := val32_lt (f := fold1 l 1) (n := 14) h1l
  rw [pow448] at hL hL1
  have hP := P_eq
  have ht : fold1C l 1 ≤ 1 := by omega
  refine ⟨ht, fun k hk => ?_, ?_⟩
  · simp only [frR, sel]; split
    · exact h1l k hk
    · exact hl k hk
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ht with h0 | h1
    · have e : val32 (frR l) 14 = val32 l 14 := val32_congr fun k _ => by simp only [frR, sel, h0]; rfl
      rw [e, Nat.mod_eq_of_lt (by omega)]
    · have e : val32 (frR l) 14 = val32 (fold1 l 1) 14 :=
        val32_congr fun k _ => by simp only [frR, sel, h1, ite_true]
      rw [e, show val32 l 14 = val32 (fold1 l 1) 14 + P by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]

end VG.Proof.X448.Limbs32

namespace VG.Proof.X448.Limbs32

open VG.Proof.X25519

/-- A number of one nonzero limb, the lowest. -/
theorem val32_single (d : Nat) {n : Nat} (hn : 0 < n) : val32 (fun k => if k = 0 then d else 0) n = d := by
  have := val32_add_head (fun _ => 0) d hn
  simp only [Nat.zero_add, val32_zero_fn] at this
  exact this

end VG.Proof.X448.Limbs32
