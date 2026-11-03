module

public import VerifiedGarbage.Proof.Weierstrass.RISCV64.P521Unsat.Pipe

/-!
# Arithmetic modulo P-521's prime in 58-bit limbs, on RISC-V: the columns' values

The columns of `mulPairs` and `sqPairs` (`Impl/Weierstrass/RISCV64/P521Unsat.lean`),
for operands whose words are the limbs `aᵢ`, `bⱼ` and the doubled limbs at
`Y`: column `c` is `lo c + 2 hi c`, its terms below and past `2⁵²²`
(`mulCol_eq`, `sqCol_eq`), so that the columns' sum and `2⁵²²` times the
part past it are the product and twice that part (`mulCols_sum`,
`sqCols_sum`), which `2⁵²² ≡ 2` makes the product modulo `p` (`mod_cancel`).
-/

@[expose] public section

-- `2⁵²²` is a numeral.
set_option exponentiation.threshold 600

namespace VG.Proof.Weierstrass.RISCV64.P521Unsat

open VG VG.RISCV64 VG.Impl.Weierstrass.RISCV64.P521Unsat

/-- The number of the limbs `f 0`, …, `f (n - 1)` in base `W`. -/
def lvW (W : Nat) (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => lvW W f n + W ^ n * f n

theorem lv_eq (f : Nat → Nat) : ∀ n, lv f n = lvW (2 ^ 58) f n
  | 0 => rfl
  | n + 1 => by rw [lv, lvW, lv_eq f n, Nat.pow_mul]

theorem sum_map_two {l : List Nat} {f : Nat → Nat} : (l.map fun i => 2 * f i).sum = 2 * (l.map f).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; omega

theorem sum_map_congr {l : List Nat} {f g : Nat → Nat} (h : ∀ i ∈ l, f i = g i) : (l.map f).sum = (l.map g).sum := by
  rw [List.map_congr_left h]

theorem tsum_map {β : Type} (f : Src × Src → Nat) (g : β → Src × Src) (l : List β) :
    tsum f (l.map g) = (l.map fun x => f (g x)).sum := by
  simp only [tsum, List.map_map]; rfl

/-! ## The product -/

/-- Column `c`'s terms below `2⁵²²`. -/
def mlo (a b : Nat → Nat) (c : Nat) : Nat := (((List.range 9).filter fun i => i ≤ c).map fun i => a i * b (c - i)).sum

/-- Column `c`'s terms past `2⁵²²`. -/
def mhi (a b : Nat → Nat) (c : Nat) : Nat := (((List.range 9).filter fun i => c < i).map fun i => a i * b (c + 9 - i)).sum

theorem mulCol_eq (v : Src → Nat) (a b : Nat → Nat) (h4 : ∀ i < 9, v (.t4, 8 * i) = a i)
    (h5 : ∀ j < 9, v (.t5, 8 * j) = b j) (hY : ∀ j < 9, v (.a3, Y + 8 * j) = 2 * b j) {c : Nat} (hc : c < 9) :
    tsum (fun q => v q.1 * v q.2) (mulPairs c) = mlo a b c + 2 * mhi a b c := by
  unfold mulPairs mlo mhi
  rw [tsum_append, tsum_map, tsum_map, ← sum_map_two]
  congr 1
  · refine sum_map_congr fun i hi => ?_
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hi
    rw [h4 i hi.1, h5 (c - i) (by omega)]
  · refine sum_map_congr fun i hi => ?_
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hi
    rw [h4 i hi.1, hY (c + 9 - i) (by omega), Nat.mul_left_comm]

/-- The columns of a product. -/
theorem mulCols_sum (a b : Nat → Nat) :
    lv (fun c => mlo a b c + 2 * mhi a b c) 9 + 2 ^ 522 * lv (mhi a b) 9 = lv a 9 * lv b 9 + 2 * lv (mhi a b) 9 := by
  simp only [lv_eq]
  rw [show (2 : Nat) ^ 522 = (2 ^ 58) ^ 9 by rw [← Nat.pow_mul]]
  generalize (2 : Nat) ^ 58 = W
  simp only [lvW, mlo, mhi, List.range_succ, List.range_zero, List.nil_append, List.filter_cons, List.filter_nil,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceLT,
    Nat.reduceAdd, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte, List.cons_append]
  grind

/-! ## The square -/

/-- Column `c`'s cross terms below `2⁵²²`, `aᵢ aⱼ` for `j < i`. -/
def scr (a : Nat → Nat) (c : Nat) : Nat :=
  (((List.range 9).filter fun i => i ≤ c ∧ c - i < i).map fun i => a i * a (c - i)).sum

/-- Column `c`'s square below `2⁵²²`. -/
def sdg (a : Nat → Nat) (c : Nat) : Nat := if c % 2 = 0 then a (c / 2) * a (c / 2) else 0

/-- Column `c`'s cross terms past `2⁵²²`. -/
def shc (a : Nat → Nat) (c : Nat) : Nat :=
  (((List.range 9).filter fun i => c < i ∧ c + 9 - i < i).map fun i => a i * a (c + 9 - i)).sum

/-- Column `c`'s square past `2⁵²²`. -/
def shd (a : Nat → Nat) (c : Nat) : Nat := if c % 2 = 1 then a ((c + 9) / 2) * a ((c + 9) / 2) else 0

/-- Column `c` of a square past `2⁵²²`. -/
def shi (a : Nat → Nat) (c : Nat) : Nat := 2 * shc a c + shd a c

theorem sqCol_eq (v : Src → Nat) (a : Nat → Nat) (h4 : ∀ i < 9, v (.t4, 8 * i) = a i)
    (hY : ∀ j < 9, v (.a3, Y + 8 * j) = 2 * a j) {c : Nat} (hc : c < 9) :
    tsum (fun q => v q.1 * v q.2) (sqPairs c) = 2 * scr a c + sdg a c + 2 * shi a c := by
  unfold sqPairs scr sdg shi shc shd
  rw [tsum_append, tsum_append, tsum_append, tsum_map, tsum_map, ← sum_map_two, ← sum_map_two]
  have e1 : (((List.range 9).filter fun i => i ≤ c ∧ c - i < i).map fun x =>
      v ((Reg.t4, 8 * x), (Reg.a3, Y + 8 * (c - x))).1 * v ((Reg.t4, 8 * x), (Reg.a3, Y + 8 * (c - x))).2).sum =
      (((List.range 9).filter fun i => i ≤ c ∧ c - i < i).map fun i => 2 * (a i * a (c - i))).sum := by
    refine sum_map_congr fun i hi => ?_
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hi
    rw [h4 i hi.1, hY (c - i) (by omega), Nat.mul_left_comm]
  have e2 : (((List.range 9).filter fun i => c < i ∧ c + 9 - i < i).map fun x =>
      v ((Reg.a3, Y + 8 * x), (Reg.a3, Y + 8 * (c + 9 - x))).1 *
        v ((Reg.a3, Y + 8 * x), (Reg.a3, Y + 8 * (c + 9 - x))).2).sum =
      (((List.range 9).filter fun i => c < i ∧ c + 9 - i < i).map fun i => 2 * (2 * (a i * a (c + 9 - i)))).sum := by
    refine sum_map_congr fun i hi => ?_
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hi
    rw [hY i hi.1, hY (c + 9 - i) (by omega)]
    rw [Nat.mul_assoc, Nat.mul_left_comm (a i), ← Nat.mul_assoc 2 2]
  rw [e1, e2, sum_map_two, sum_map_two, sum_map_two]
  have d1 : tsum (fun q => v q.1 * v q.2)
      (if c % 2 = 0 then [((Reg.t4, 8 * (c / 2)), (Reg.t4, 8 * (c / 2)))] else []) =
      if c % 2 = 0 then a (c / 2) * a (c / 2) else 0 := by
    split
    · rw [tsum_singleton, h4 _ (by omega)]
    · rfl
  have d2 : tsum (fun q => v q.1 * v q.2)
      (if c % 2 = 1 then [((Reg.t4, 8 * ((c + 9) / 2)), (Reg.a3, Y + 8 * ((c + 9) / 2)))] else []) =
      2 * (if c % 2 = 1 then a ((c + 9) / 2) * a ((c + 9) / 2) else 0) := by
    split
    · rw [tsum_singleton]
      dsimp only
      rw [h4 _ (by omega), hY _ (by omega), Nat.mul_left_comm]
    · rfl
  rw [d1, d2]
  omega

/-- The columns of a square. -/
theorem sqCols_sum (a : Nat → Nat) :
    lv (fun c => 2 * scr a c + sdg a c + 2 * shi a c) 9 + 2 ^ 522 * lv (shi a) 9 =
      lv a 9 * lv a 9 + 2 * lv (shi a) 9 := by
  simp only [lv_eq]
  rw [show (2 : Nat) ^ 522 = (2 ^ 58) ^ 9 by rw [← Nat.pow_mul]]
  generalize (2 : Nat) ^ 58 = W
  simp only [lvW, scr, sdg, shi, shc, shd, List.range_succ, List.range_zero, List.nil_append, List.filter_cons,
    List.filter_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceSub, Nat.reduceLeDiff,
    Nat.reduceLT, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, decide_true, decide_false, Bool.false_eq_true,
    ↓reduceIte, List.cons_append, and_self, and_true, and_false, Nat.lt_irrefl]
  grind

/-! ## Modulo `p` -/

theorem mod_cancel {x y K : Nat} (h : x + 2 ^ 522 * K = y + 2 * K) : x % p = y % p := by
  have e : (2 : Nat) ^ 522 = 2 * p + 2 := by
    have h1 : (2 : Nat) ^ 522 = 2 ^ 521 * 2 := Nat.pow_succ ..
    have h2 := Nat.one_le_two_pow (n := 521)
    show (2 : Nat) ^ 522 = 2 * (2 ^ 521 - 1) + 2
    omega
  rw [e] at h
  have : y = x + p * (2 * K) := by
    have : (2 * p + 2) * K = p * (2 * K) + 2 * K := by
      rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_left_comm]
    omega
  rw [this, Nat.add_mul_mod_self_left]

end VG.Proof.Weierstrass.RISCV64.P521Unsat
