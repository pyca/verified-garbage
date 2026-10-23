module
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Spec.X25519

import VerifiedGarbage.Proof.X25519.Field

/-!
# X25519 on PPC64LE: numbers of 32-bit limbs

The arithmetic of `Impl/X25519/PPC64LE.lean` on natural numbers: a number of
limbs (`val32`), the limbs of a number carried from sums (`chain`, `out`), a
row of a product (Knuth's algorithm M), the fold of a product's top half
(`2²⁵⁶ ≡ 38`), the carry out folded in again (`tail`), `4p` as limbs, and the
final reduction.
-/

@[expose] public section

namespace VG.Proof.X25519.PPC64LE

open VG.Spec.X25519 (P)

/-- The number with the limbs `f 0, …, f (n - 1)` in radix `2³²` (limbs of any
size). -/
def val32 (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => val32 f n + 2 ^ (32 * n) * f n

theorem val32_succ (f : Nat → Nat) (n : Nat) : val32 f (n + 1) = val32 f n + 2 ^ (32 * n) * f n :=
  rfl

theorem pow32_succ (n : Nat) : 2 ^ (32 * (n + 1)) = 2 ^ (32 * n) * 2 ^ 32 := by
  rw [Nat.mul_succ, Nat.pow_add]

theorem val32_congr {f g : Nat → Nat} : ∀ {n : Nat}, (∀ k < n, f k = g k) → val32 f n = val32 g n
  | 0, _ => rfl
  | n + 1, h => by
    rw [val32_succ, val32_succ, val32_congr (fun k hk => h k (by omega)), h n (by omega)]

theorem val32_lt {f : Nat → Nat} : ∀ {n : Nat}, (∀ k < n, f k < 2 ^ 32) → val32 f n < 2 ^ (32 * n)
  | 0, _ => Nat.one_pos
  | n + 1, h => by
    have ih := val32_lt (n := n) fun k hk => h k (by omega)
    have h1 : 2 ^ (32 * n) * f n ≤ 2 ^ (32 * n) * (2 ^ 32 - 1) :=
      Nat.mul_le_mul_left _ (by have := h n (by omega); omega)
    rw [val32_succ, pow32_succ, Nat.mul_sub_one] at *
    omega

theorem val32_add (f g : Nat → Nat) :
    ∀ n, val32 (fun k => f k + g k) n = val32 f n + val32 g n
  | 0 => rfl
  | n + 1 => by rw [val32_succ, val32_succ, val32_succ, val32_add f g n, Nat.mul_add]; omega

theorem val32_cmul (a : Nat) (f : Nat → Nat) : ∀ n, val32 (fun k => a * f k) n = a * val32 f n
  | 0 => rfl
  | n + 1 => by
    rw [val32_succ, val32_succ, val32_cmul a f n, Nat.mul_add, Nat.mul_left_comm]

theorem val32_append (f : Nat → Nat) (m : Nat) :
    ∀ n, val32 f (m + n) = val32 f m + 2 ^ (32 * m) * val32 (fun k => f (m + k)) n
  | 0 => by simp [val32]
  | n + 1 => by
    rw [← Nat.add_assoc, val32_succ, val32_append f m n, val32_succ, Nat.mul_add (2 ^ (32 * m)),
      ← Nat.mul_assoc, ← Nat.pow_add, Nat.mul_add 32 m n]
    omega

theorem val32_zero_fn : ∀ n, val32 (fun _ => 0) n = 0
  | 0 => rfl
  | n + 1 => by rw [val32_succ, val32_zero_fn n]; rfl

theorem val32_mono (f : Nat → Nat) {m n : Nat} (h : m ≤ n) : val32 f m ≤ val32 f n := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [val32_append]; exact Nat.le_add_right _ _

theorem val32_head (f : Nat → Nat) {n : Nat} (hn : 0 < n) : f 0 ≤ val32 f n := by
  have := val32_mono f (m := 1) (n := n) hn
  simp only [val32] at this
  omega

/-- Changing limb 0 by `d`. -/
theorem val32_add_head (f : Nat → Nat) (d : Nat) {n : Nat} (hn : 0 < n) :
    val32 (fun k => if k = 0 then f 0 + d else f k) n = val32 f n + d := by
  have e : val32 (fun k => if k = 0 then f 0 + d else f k) n =
      val32 (fun k => f k + if k = 0 then d else 0) n :=
    val32_congr fun k _ => by by_cases h : k = 0 <;> simp [h]
  rw [e, val32_add]
  congr 1
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  rw [Nat.add_comm, val32_append, show val32 (fun k => if k = 0 then d else 0) 1 = d by simp [val32]]
  rw [val32_congr (g := fun _ => 0) (fun k _ => by simp), val32_zero_fn, Nat.mul_zero, Nat.add_zero]

/-! ## Carrying -/

/-- The carry into limb `k` of the limbs of `Σ c k 2^(32k) + cin`. -/
def chain (c : Nat → Nat) (cin : Nat) : Nat → Nat
  | 0 => cin
  | k + 1 => (c k + chain c cin k) / 2 ^ 32

/-- Limb `k` of the limbs of `Σ c k 2^(32k) + cin`. -/
def out (c : Nat → Nat) (cin k : Nat) : Nat := (c k + chain c cin k) % 2 ^ 32

theorem chain_succ (c : Nat → Nat) (cin k : Nat) :
    chain c cin (k + 1) = (c k + chain c cin k) / 2 ^ 32 := rfl

theorem out_lt (c : Nat → Nat) (cin k : Nat) : out c cin k < 2 ^ 32 := Nat.mod_lt _ (by decide)

theorem chain_val (c : Nat → Nat) (cin : Nat) :
    ∀ n, val32 (out c cin) n + 2 ^ (32 * n) * chain c cin n = val32 c n + cin
  | 0 => by simp [val32, chain]
  | n + 1 => by
    have ih := chain_val c cin n
    rw [val32_succ, val32_succ, chain_succ, pow32_succ, out]
    have e : 2 ^ (32 * n) * ((c n + chain c cin n) % 2 ^ 32) +
        2 ^ (32 * n) * 2 ^ 32 * ((c n + chain c cin n) / 2 ^ 32) = 2 ^ (32 * n) * (c n + chain c cin n) := by
      rw [Nat.mul_assoc, ← Nat.mul_add, Nat.mod_add_div]
    rw [Nat.mul_add] at e
    omega

/-- The carries stay below `2³²` (and each sum below `2⁶⁴`) if every sum is at
most `2⁶⁴ - 2³²`. -/
theorem chain_lt {c : Nat → Nat} {cin n : Nat} (hc : ∀ k < n, c k + 2 ^ 32 ≤ 2 ^ 64)
    (hcin : cin < 2 ^ 32) : ∀ k ≤ n, chain c cin k < 2 ^ 32
  | 0, _ => hcin
  | k + 1, hk => by
    have := chain_lt hc hcin k (by omega)
    have := hc k (by omega)
    rw [chain_succ, Nat.div_lt_iff_lt_mul (by decide)]
    omega

theorem sum_lt {c : Nat → Nat} {cin n : Nat} (hc : ∀ k < n, c k + 2 ^ 32 ≤ 2 ^ 64)
    (hcin : cin < 2 ^ 32) {k : Nat} (hk : k < n) : c k + chain c cin k < 2 ^ 64 := by
  have := chain_lt hc hcin k (by omega)
  have := hc k hk
  omega

/-! ## A row of a product -/

/-- Row `i` of a product: the sums `a_i b_j + acc_(i+j)`. -/
def rowC (acc a b : Nat → Nat) (i j : Nat) : Nat := a i * b j + acc (i + j)

/-- The limbs after row `i`: those below `i`, the row's limbs, and its carry. -/
def rowAcc (acc a b : Nat → Nat) (i k : Nat) : Nat :=
  if k < i then acc k else if k < i + 8 then out (rowC acc a b i) 0 (k - i)
  else chain (rowC acc a b i) 0 8

theorem row_val {acc a b : Nat → Nat} {i : Nat} (hv : val32 acc (i + 8) = val32 a i * val32 b 8) :
    val32 (rowAcc acc a b i) (i + 9) = val32 a (i + 1) * val32 b 8 := by
  have e1 : val32 (rowAcc acc a b i) i = val32 acc i :=
    val32_congr fun k hk => by simp [rowAcc, hk]
  have e2 : val32 (fun k => rowAcc acc a b i (i + k)) 9 =
      val32 (out (rowC acc a b i) 0) 8 + 2 ^ 256 * chain (rowC acc a b i) 0 8 := by
    rw [val32_succ, val32_congr (g := out (rowC acc a b i) 0) fun k hk => by
      simp only [rowAcc, show ¬ i + k < i by omega, show i + k < i + 8 by omega, ite_false, ite_true,
        Nat.add_sub_cancel_left]]
    simp only [rowAcc, show ¬ i + 8 < i by omega, Nat.lt_irrefl, ite_false]
  have e3 : val32 (rowC acc a b i) 8 = a i * val32 b 8 + val32 (fun k => acc (i + k)) 8 := by
    rw [← val32_cmul, ← val32_add]; rfl
  have hc := chain_val (rowC acc a b i) 0 8
  rw [show 32 * 8 = 256 from rfl, Nat.add_zero, e3] at hc
  rw [val32_append _ i 9, e1, e2, hc, val32_succ a i, Nat.add_mul, ← hv, val32_append acc i 8,
    Nat.mul_add, Nat.mul_assoc]
  omega

theorem rowC_le {acc a b : Nat → Nat} {i j : Nat} (ha : a i < 2 ^ 32) (hb : b j < 2 ^ 32)
    (hacc : acc (i + j) < 2 ^ 32) : rowC acc a b i j + 2 ^ 32 ≤ 2 ^ 64 := by
  simp only [rowC]
  have : a i * b j ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have e : (2 ^ 32 - 1) * (2 ^ 32 - 1) = 2 ^ 64 - 2 ^ 33 + 1 := by decide
  omega

theorem rowAcc_lt {acc a b : Nat → Nat} {i : Nat} (hacc : ∀ k < i, acc k < 2 ^ 32)
    (hc : ∀ j < 8, rowC acc a b i j + 2 ^ 32 ≤ 2 ^ 64) :
    ∀ k < i + 9, rowAcc acc a b i k < 2 ^ 32 := by
  intro k _
  simp only [rowAcc]
  split
  · exact hacc k (by omega)
  · split
    · exact out_lt _ _ _
    · exact chain_lt hc (by decide) 8 (Nat.le_refl _)

/-! ## The fold of a product and the tail -/

/-- The sums `lo_k + 38 hi_k` of a product's limbs. -/
def foldC (acc : Nat → Nat) (k : Nat) : Nat := acc k + 38 * acc (8 + k)

theorem foldC_le {acc : Nat → Nat} (h : ∀ k < 16, acc k < 2 ^ 32) :
    ∀ k < 8, foldC acc k + 2 ^ 32 ≤ 2 ^ 64 := by
  intro k hk
  have := h k (by omega)
  have := h (8 + k) (by omega)
  simp only [foldC]
  omega

theorem val32_foldC (acc : Nat → Nat) :
    val32 (foldC acc) 8 = val32 acc 8 + 38 * val32 (fun k => acc (8 + k)) 8 := by
  rw [← val32_cmul, ← val32_add]; rfl

/-- The final limbs of `tail`: limb 0 plus 38 times the carry out. -/
def tailL (l : Nat → Nat) (c8 k : Nat) : Nat :=
  if k = 0 then out l (38 * c8) 0 + 38 * chain l (38 * c8) 8 else out l (38 * c8) k

theorem tail_facts {l : Nat → Nat} (hl : ∀ k < 8, l k < 2 ^ 32) {c8 : Nat} (hc : c8 ≤ 38) :
    chain l (38 * c8) 8 ≤ 1 ∧ (∀ k < 8, tailL l c8 k < 2 ^ 32) ∧
      val32 (tailL l c8) 8 % P = (val32 l 8 + 2 ^ 256 * c8) % P := by
  have hv := chain_val l (38 * c8) 8
  have hL := val32_lt (f := l) (n := 8) hl
  have hO := val32_lt (f := out l (38 * c8)) (n := 8) fun k _ => out_lt _ _ _
  have h0 := val32_head (out l (38 * c8)) (n := 8) (by decide)
  rw [show 32 * 8 = 256 from rfl] at hv hL hO
  have ht : chain l (38 * c8) 8 ≤ 1 := by
    have : 2 ^ 256 * chain l (38 * c8) 8 < 2 ^ 256 * 2 := by omega
    have := Nat.lt_of_mul_lt_mul_left this
    omega
  refine ⟨ht, fun k hk => ?_, ?_⟩
  · simp only [tailL]
    split
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ht with h | h
      · rw [h]; exact out_lt _ _ _
      · rw [h] at hv ⊢; omega
    · exact out_lt _ _ _
  · have e : val32 (tailL l c8) 8 = val32 (out l (38 * c8)) 8 + 38 * chain l (38 * c8) 8 :=
      val32_add_head (out l (38 * c8)) _ (by decide)
    rw [e, ← Proof.X25519.fold256, hv, Proof.X25519.fold256]

/-! ## Sums and differences -/

/-- Limb `k` of `4p`. -/
def fourP (k : Nat) : Nat := if k = 0 then 2 ^ 34 - 76 else if k = 7 then 2 ^ 33 - 4 else 2 ^ 34 - 4

theorem val32_fourP : val32 fourP 8 = 4 * P := by decide

theorem fourP_ge : ∀ k < 8, 2 ^ 32 - 1 ≤ fourP k := by decide

theorem fourP_le : ∀ k < 8, fourP k ≤ 2 ^ 34 := by decide

/-- The sums of a difference: `a_k + 4p_k - b_k`. -/
def subC (a b : Nat → Nat) (k : Nat) : Nat := a k + fourP k - b k

theorem subC_facts {a b : Nat → Nat} (ha : ∀ k < 8, a k < 2 ^ 32) (hb : ∀ k < 8, b k < 2 ^ 32) :
    (∀ k < 8, subC a b k + 2 ^ 32 ≤ 2 ^ 64) ∧ val32 (subC a b) 8 + val32 b 8 = val32 a 8 + 4 * P := by
  have hK := fourP_ge
  refine ⟨fun k hk => ?_, ?_⟩
  · have := ha k hk; have := hb k hk
    have := fourP_le k hk
    simp only [subC]; omega
  · rw [← val32_add, ← val32_fourP, ← val32_add]
    exact val32_congr fun k hk => by have := hK k hk; have := hb k hk; simp only [subC]; omega

/-- The carry out of the limbs of a sum or difference of numbers below
`2²⁵⁶` is at most 38 (it is at most 2). -/
theorem carry_le {c : Nat → Nat} (h : val32 c 8 < 39 * 2 ^ 256) : chain c 0 8 ≤ 38 := by
  have hv := chain_val c 0 8
  rw [show 32 * 8 = 256 from rfl] at hv
  have : 2 ^ 256 * chain c 0 8 < 2 ^ 256 * 39 := by omega
  have := Nat.lt_of_mul_lt_mul_left this
  omega

/-! ## The final reduction -/

/-- `c` if `sw = 1`, else `a`. -/
def sel {α : Type} (sw : Nat) (a c : α) : α := if sw = 1 then c else a

/-- Limb 7 cut to 31 bits: the number modulo `2²⁵⁵`. -/
def mask31 (l : Nat → Nat) (k : Nat) : Nat := if k = 7 then l 7 % 2 ^ 31 else l k

theorem mask31_facts {l : Nat → Nat} (hl : ∀ k < 8, l k < 2 ^ 32) :
    val32 l 8 = val32 (mask31 l) 8 + 2 ^ 255 * (l 7 / 2 ^ 31) ∧ val32 (mask31 l) 8 < 2 ^ 255 ∧
      (∀ k < 8, mask31 l k < 2 ^ 32) ∧ l 7 / 2 ^ 31 ≤ 1 := by
  have e : val32 (mask31 l) 7 = val32 l 7 := val32_congr fun k hk => by simp [mask31, show k ≠ 7 by omega]
  have h7 := hl 7 (by decide)
  have hlo := val32_lt (f := l) (n := 7) fun k hk => hl k (by omega)
  rw [show 32 * 7 = 224 from rfl] at hlo
  have hm : l 7 = l 7 % 2 ^ 31 + 2 ^ 31 * (l 7 / 2 ^ 31) := (Nat.mod_add_div _ _).symm
  refine ⟨?_, ?_, fun k hk => ?_, by omega⟩
  · rw [val32_succ l 7, val32_succ (mask31 l) 7, e, show mask31 l 7 = l 7 % 2 ^ 31 from rfl,
      show 32 * 7 = 224 from rfl]
    conv => lhs; rw [hm]
    rw [Nat.mul_add, show (2 : Nat) ^ 255 = 2 ^ 224 * 2 ^ 31 from rfl, Nat.mul_assoc]; omega
  · rw [val32_succ (mask31 l) 7, e, show mask31 l 7 = l 7 % 2 ^ 31 from rfl, show 32 * 7 = 224 from rfl]
    have : 2 ^ 224 * (l 7 % 2 ^ 31) ≤ 2 ^ 224 * (2 ^ 31 - 1) :=
      Nat.mul_le_mul_left _ (by have := Nat.mod_lt (l 7) (show 2 ^ 31 > 0 by decide); omega)
    rw [show (2 : Nat) ^ 255 = 2 ^ 224 * 2 ^ 31 from rfl]
    rw [Nat.mul_sub_one] at this
    omega
  · simp only [mask31]; split
    · exact Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)
    · exact hl k hk

/-- The limbs of `x' = x mod 2²⁵⁵ + 19 (x >> 255)`. -/
def frA (l : Nat → Nat) : Nat → Nat := out (mask31 l) (19 * (l 7 / 2 ^ 31))

/-- The limbs of `x' + 19`. -/
def frY (l : Nat → Nat) : Nat → Nat := out (frA l) 19

/-- Whether `x' + 19 ≥ 2²⁵⁵`, that is `x' ≥ p`. -/
def frS (l : Nat → Nat) : Nat := frY l 7 / 2 ^ 31

/-- The limbs of `x mod p`. -/
def frR (l : Nat → Nat) (k : Nat) : Nat := sel (frS l) (frA l k) (mask31 (frY l) k)

theorem freeze_facts {l : Nat → Nat} (hl : ∀ k < 8, l k < 2 ^ 32) :
    chain (mask31 l) (19 * (l 7 / 2 ^ 31)) 8 = 0 ∧ chain (frA l) 19 8 = 0 ∧ frS l ≤ 1 ∧
      (∀ k < 8, frR l k < 2 ^ 32) ∧ val32 (frR l) 8 = val32 l 8 % P := by
  obtain ⟨e1, b1, lm, c1⟩ := mask31_facts hl
  have hA := chain_val (mask31 l) (19 * (l 7 / 2 ^ 31)) 8
  rw [show 32 * 8 = 256 from rfl] at hA
  have tA : chain (mask31 l) (19 * (l 7 / 2 ^ 31)) 8 = 0 := by
    rcases Nat.eq_zero_or_pos (chain (mask31 l) (19 * (l 7 / 2 ^ 31)) 8) with h | h
    · exact h
    · have : 2 ^ 256 ≤ 2 ^ 256 * chain (mask31 l) (19 * (l 7 / 2 ^ 31)) 8 := Nat.le_mul_of_pos_right _ h
      omega
  rw [tA, Nat.mul_zero, Nat.add_zero] at hA
  have hY := chain_val (frA l) 19 8
  rw [show 32 * 8 = 256 from rfl] at hY
  have hAl : ∀ k < 8, frA l k < 2 ^ 32 := fun k _ => out_lt _ _ _
  have hYl : ∀ k < 8, frY l k < 2 ^ 32 := fun k _ => out_lt _ _ _
  have tY : chain (frA l) 19 8 = 0 := by
    rcases Nat.eq_zero_or_pos (chain (frA l) 19 8) with h | h
    · exact h
    · have : 2 ^ 256 ≤ 2 ^ 256 * chain (frA l) 19 8 := Nat.le_mul_of_pos_right _ h
      have : val32 (frA l) 8 = val32 (mask31 l) 8 + 19 * (l 7 / 2 ^ 31) := hA
      omega
  rw [tY, Nat.mul_zero, Nat.add_zero] at hY
  obtain ⟨e2, b2, lm2, c2⟩ := mask31_facts hYl
  have hxA : val32 (frA l) 8 = val32 (mask31 l) 8 + 19 * (l 7 / 2 ^ 31) := hA
  have hyv : val32 (frY l) 8 = val32 (frA l) 8 + 19 := hY
  have hP : P = 2 ^ 255 - 19 := rfl
  have hx : val32 l 8 % P = val32 (frA l) 8 % P := by
    rw [e1, hxA, Proof.X25519.fold255]
  refine ⟨tA, tY, c2, fun k hk => ?_, ?_⟩
  · simp only [frR, sel]; split
    · exact lm2 k hk
    · exact hAl k hk
  · rw [hx]
    have hs : frS l = frY l 7 / 2 ^ 31 := rfl
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp c2 with h0 | h1
    · have e : val32 (frR l) 8 = val32 (frA l) 8 :=
        val32_congr fun k _ => by simp only [frR, sel, hs, h0]; rfl
      rw [e, Nat.mod_eq_of_lt (by rw [h0] at e2; omega)]
    · have e : val32 (frR l) 8 = val32 (mask31 (frY l)) 8 :=
        val32_congr fun k _ => by simp only [frR, sel, hs, h1, ite_true]
      rw [e]
      rw [h1] at e2
      have : val32 (frA l) 8 = val32 (mask31 (frY l)) 8 + P := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-- The limbs of a number of `n` limbs below `2³²`. -/
theorem val32_div {r : Nat → Nat} {n : Nat} (hr : ∀ k < n, r k < 2 ^ 32) {k : Nat} (hk : k < n) :
    val32 r n / 2 ^ (32 * k) % 2 ^ 32 = r k := by
  have e := val32_append r k (n - k)
  rw [Nat.add_sub_cancel' (by omega)] at e
  have e' := val32_append (fun j => r (k + j)) 1 (n - k - 1)
  rw [Nat.add_sub_cancel' (by omega)] at e'
  simp only [val32, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.add_zero] at e'
  have hlt := val32_lt (f := r) (n := k) fun j hj => hr j (by omega)
  rw [e, e', Nat.mul_comm (2 ^ (32 * k)), Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
    Nat.div_eq_of_lt hlt, Nat.zero_add, show (2 : Nat) ^ (32 * 1) = 2 ^ 32 from rfl, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (hr k hk)]

end VG.Proof.X25519.PPC64LE
