module

import VerifiedGarbage.Proof.X25519.X86.Arith
public import VerifiedGarbage.Proof.X25519.X86.Column
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Spec.X448
import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.X448.X86.Mem
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.X448.X86.Instr
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.X448.X86.Columns
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.X448.X86.Field

/-!
# X448 on x86 (32-bit): numbers of 32-bit words

The arithmetic of `vg_gf448_r16_mul`'s product (`Impl/X448/X86.lean`): the
columns of a product of two numbers of `n` words (`conv_identity`), the
fold of its 28 words by `2^448 = 2^224 + 1` (`foldCol_mod`), the two folds
of the carry (`fold_carries`), and the words of an element from its limbs
(`num_pack`).
-/

@[expose] public section

namespace VG.Proof.X448.X86

open VG VG.Proof.X448.Radix16
open VG.Proof.X25519.X86 (num num_succ num_congr num_add num_mul num_lt)

theorem num_zero (n : Nat) : num (fun _ => 0) n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [num_succ, ih, Nat.mul_zero]

theorem num_split (f : Nat → Nat) (a b : Nat) :
    num f (a + b) = num f a + (2 ^ 32) ^ a * num (fun i => f (a + i)) b := by
  induction b with
  | zero => simp only [Nat.add_zero, num, Nat.mul_zero]
  | succ b ih =>
    rw [Nat.add_succ, num_succ, num_succ, ih, Nat.pow_add, Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

/-- A number shifted up by `m` words. -/
theorem num_shift (g : Nat → Nat) (m N : Nat) :
    num (fun k => if m ≤ k then g (k - m) else 0) (m + N) = (2 ^ 32) ^ m * num g N := by
  rw [num_split, num_congr (g := fun _ => 0) (fun k hk => if_neg (by omega_arith)), num_zero, Nat.zero_add]
  exact congrArg (_ * ·) (num_congr fun i _ => by
    simp only [Nat.le_add_right, ite_true, Nat.add_sub_cancel_left])

/-- A number of `n` words, read as one of more. -/
theorem num_trunc (h : Nat → Nat) (n d : Nat) :
    num (fun j => if j < n then h j else 0) (n + d) = num h n := by
  rw [num_split, num_congr (g := h) (fun k hk => if_pos hk),
    num_congr (f := fun i => if n + i < n then h (n + i) else 0) (g := fun _ => 0)
      (fun i _ => if_neg (by omega_arith)), num_zero, Nat.mul_zero, Nat.add_zero]

/-- Column `k` of the product of two numbers of `n` words: the products
`a_i b_j` with `i + j = k`. -/
def convCol (n : Nat) (fa fb : Nat → Nat) (k : Nat) : Nat :=
  (((List.range n).filter fun i => i ≤ k && k - i < n).map fun i => fa i * fb (k - i)).sum

/-- The columns of the first `m` words of `a` times `b`. -/
theorem conv_rows (n : Nat) (fa fb : Nat → Nat) (N : Nat) : ∀ m, m + n ≤ N →
    num (fun k => (((List.range m).filter fun i => i ≤ k && k - i < n).map fun i => fa i * fb (k - i)).sum) N =
      num fa m * num fb n
  | 0, _ => by
    simp only [List.range_zero, List.filter_nil, List.map_nil, List.sum_nil, num_zero, num, Nat.zero_mul]
  | m + 1, h => by
    have e : ∀ k < N, (((List.range (m + 1)).filter fun i => i ≤ k && k - i < n).map
          fun i => fa i * fb (k - i)).sum =
        (((List.range m).filter fun i => i ≤ k && k - i < n).map fun i => fa i * fb (k - i)).sum +
          (if m ≤ k then (if k - m < n then fa m * fb (k - m) else 0) else 0) := by
      intro k _
      rw [List.range_succ, List.filter_append, List.map_append, List.sum_append]
      by_cases h1 : m ≤ k <;> by_cases h2 : k - m < n <;>
        simp only [List.filter_cons, List.filter_nil, h1, h2, decide_true, decide_false, Bool.and_self,
          Bool.and_false, Bool.false_and, ite_true, ite_false, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil, Bool.false_eq_true]
    rw [num_congr e, num_add, conv_rows n fa fb N m (by omega_arith), num_succ, Nat.add_mul]
    obtain ⟨d, rfl⟩ : ∃ d, N = m + (n + d) := ⟨N - m - n, by omega_arith⟩
    rw [num_shift (fun j => if j < n then fa m * fb j else 0), num_trunc, num_mul, Nat.mul_assoc]

/-- Product scanning: the columns of `a b`, for numbers of `n` words. -/
theorem conv_identity (n : Nat) (fa fb : Nat → Nat) :
    num (convCol n fa fb) (2 * n) = num fa n * num fb n :=
  conv_rows n fa fb (2 * n) n (by omega_arith)

theorem convCol_le {n : Nat} {fa fb : Nat → Nat} {M : Nat} (h : ∀ i j, fa i * fb j ≤ M) (k : Nat) :
    convCol n fa fb k ≤ n * M := by
  unfold convCol
  generalize ((List.range n).filter fun i => i ≤ k && k - i < n) = l at *
  have hl : ((List.range n).filter fun i => i ≤ k && k - i < n).length ≤ n :=
    Nat.le_trans (List.length_filter_le _ _) (by rw [List.length_range]; exact Nat.le_refl _)
  sorry

/-! ## The fold by the prime -/

theorem pow7 : ((2 : Nat) ^ 32) ^ 7 = half := by decide +kernel
theorem pow14 : ((2 : Nat) ^ 32) ^ 14 = full := by decide +kernel

/-- Column `k` of the product's 28 words folded by `2^448 = 2^224 + 1`. -/
def foldCol (p : Nat → Nat) (k : Nat) : Nat :=
  p k + p (k + 14) + if k < 7 then p (k + 21) else p (k + 7) + p (k + 14)

theorem foldCol_val (p : Nat → Nat) :
    num (foldCol p) 14 =
      (num p 7 + num (fun i => p (14 + i)) 7 + num (fun i => p (21 + i)) 7) +
      half * (num (fun i => p (7 + i)) 7 + num (fun i => p (21 + i)) 7 +
        num (fun i => p (14 + i)) 7 + num (fun i => p (21 + i)) 7) := by
  rw [show 14 = 7 + 7 from rfl, num_split, pow7]
  apply congrArg₂ (· + ·)
  · rw [← num_add, ← num_add]
    apply num_congr
    intro i hi
    simp only [foldCol, ite_eq_left hi, Nat.add_comm i]
  · apply congrArg (half * ·)
    rw [← num_add, ← num_add, ← num_add]
    apply num_congr
    intro i _
    simp only [foldCol, ite_eq_right (by omega_arith : ¬ 7 + i < 7)]
    rw [show 7 + i + 14 = 21 + i by omega_arith, show 7 + i + 7 = 14 + i by omega_arith]
    omega_arith

theorem foldCol_mod (p : Nat → Nat) : num (foldCol p) 14 % Spec.X448.P = num p 28 % Spec.X448.P := by
  have hp : Spec.X448.P = full - half - 1 := by decide +kernel
  have he : num p 28 = num (foldCol p) 14 +
      Spec.X448.P * (num (fun i => p (14 + i)) 7 + (half + 1) * num (fun i => p (21 + i)) 7) := by
    rw [foldCol_val, show 28 = 14 + 14 from rfl, num_split, pow14,
      show 14 = 7 + 7 from rfl, num_split, num_split, pow7]
    simp only [← Nat.add_assoc, Nat.reduceAdd]
    simp only [hp, full, half, radix, Nat.reducePow]
    omega_arith
  rw [he, Nat.add_mul_mod_self_left]

theorem foldCol_lt {p : Nat → Nat} (h : ∀ i < 28, p i < 2 ^ 32) : num (foldCol p) 14 < 4 * full := by
  have b : ∀ d, d + 7 ≤ 28 → num (fun i => p (d + i)) 7 < half := fun d hd => by
    rw [← pow7]; exact num_lt fun i hi => h _ (by omega_arith)
  have b0 : num p 7 < half := by rw [← pow7]; exact num_lt fun i hi => h _ (by omega_arith)
  have b1 := b 7 (by decide); have b2 := b 14 (by decide); have b3 := b 21 (by decide)
  have hh : half * half = full := by decide +kernel
  rw [foldCol_val]
  generalize num (fun i => p (7 + i)) 7 = x1 at *
  generalize num (fun i => p (14 + i)) 7 = x2 at *
  generalize num (fun i => p (21 + i)) 7 = x3 at *
  have m := Nat.mul_le_mul_left half (show x1 + x3 + x2 + x3 ≤ 4 * (half - 1) by omega_arith)
  have hpos : 0 < half := by decide
  rw [Nat.mul_left_comm, Nat.mul_sub, hh, Nat.mul_one] at m
  omega_arith

/-- The carry `c` added to words 0 and 7. -/
theorem carry_val (r : Nat → Nat) (c : Nat) :
    num (fun k => r k + if k = 0 ∨ k = 7 then c else 0) 14 = num r 14 + (half + 1) * c := by
  rw [num_add]
  apply congrArg (num r 14 + ·)
  rw [show 14 = 7 + 7 from rfl, num_split, pow7]
  simp only [num]
  simp (config := {decide := true}) only [ite_true, ite_false, Nat.mul_zero, Nat.add_zero,
    Nat.zero_add, Nat.pow_zero, Nat.one_mul, Nat.reduceAdd]
  rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]

/-- The words `r1` and the carry `c1` of the folded product, after the carry
is folded twice: the second fold does not carry. -/
theorem fold_carries {V r1 c1 r2 c2 r3 c3 : Nat} (h1 : r1 + full * c1 = V) (hc1 : c1 ≤ 3)
    (b1 : r1 < full) (h2 : r2 + full * c2 = r1 + (half + 1) * c1)
    (h3 : r3 + full * c3 = r2 + (half + 1) * c2) :
    c3 = 0 ∧ r3 % Spec.X448.P = V % Spec.X448.P := by
  have small : 4 * (half + 1) < full := by decide +kernel
  have m1 : (half + 1) * c1 ≤ (half + 1) * 3 := Nat.mul_le_mul_left _ hc1
  have hc2 : c2 ≤ 1 := by
    by_contra hc
    have hp := Nat.mul_le_mul_left full (show 2 ≤ c2 by omega_arith)
    omega_arith
  have hc3 : c3 = 0 := by
    by_contra hn
    have hp := Nat.mul_le_mul_left full (show 1 ≤ c3 from Nat.pos_of_ne_zero hn)
    rcases Nat.eq_zero_or_pos c2 with hc | hc
    · rw [hc, Nat.mul_zero, Nat.add_zero] at h3 h2; omega_arith
    · have hc : c2 = 1 := by omega_arith
      rw [hc, Nat.mul_one] at h2 h3
      omega_arith
  refine ⟨hc3, ?_⟩
  rw [hc3, Nat.mul_zero, Nat.add_zero] at h3
  rw [h3, ← fold_mod, h2, ← fold_mod, h1]

/-! ## Words and limbs -/

/-- The number of the words that pack the limbs in pairs. -/
theorem num_pack {w l : Nat → Nat} : ∀ n, (∀ k < n, w k = l (2 * k) + 2 ^ 16 * l (2 * k + 1)) →
    num w n = valN l (2 * n)
  | 0, _ => rfl
  | n + 1, h => by
    rw [num_succ, num_pack n fun k hk => h k (by omega_arith), h n (by omega_arith),
      show 2 * (n + 1) = 2 * n + 1 + 1 from rfl, valN_succ, valN_succ, Nat.pow_succ radix,
      show (2 ^ 32 : Nat) ^ n = radix ^ (2 * n) by rw [radix, ← Nat.pow_mul, ← Nat.pow_mul]; rfl]
    simp only [radix, Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

end VG.Proof.X448.X86
