import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.X25519.Bytes

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.Arm.Limbs`. -/
section

/-!
# X25519 on 32-bit ARM: numbers of 16-bit limbs

The arithmetic of `Impl/X25519/Arm.lean` on natural numbers: a number of limbs
(`val16`), the limbs of a number carried from sums (`chain`, `out`), a row of
a product (Knuth's algorithm M), the fold of a product's top half (`2²⁵⁶ ≡
38`), the carry out folded in again (`tail`), `4p` as limbs, and the final
reduction.
-/

namespace VG.Proof.X25519.Arm

open VG.Spec.X25519 (P)

/-- The number with the limbs `f 0, …, f (n - 1)` in radix `2¹⁶` (limbs of any
size). -/
def val16 (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => VG.Proof.X25519.Arm.val16 f n + 2 ^ (16 * n) * f n

theorem val16_succ (f : Nat → Nat) (n : Nat) : VG.Proof.X25519.Arm.val16 f (n + 1) = VG.Proof.X25519.Arm.val16 f n + 2 ^ (16 * n) * f n :=
  rfl

theorem pow16_succ (n : Nat) : 2 ^ (16 * (n + 1)) = 2 ^ (16 * n) * 65536 := by
  rw [Nat.mul_succ, Nat.pow_add]

theorem val16_congr {f g : Nat → Nat} : ∀ {n : Nat}, (∀ k < n, f k = g k) → VG.Proof.X25519.Arm.val16 f n = VG.Proof.X25519.Arm.val16 g n
  | 0, _ => rfl
  | n + 1, h => by
    rw [VG.Proof.X25519.Arm.val16_succ, VG.Proof.X25519.Arm.val16_succ, VG.Proof.X25519.Arm.val16_congr (fun k hk => h k (by omega)), h n (by omega)]

theorem val16_lt {f : Nat → Nat} : ∀ {n : Nat}, (∀ k < n, f k < 65536) → VG.Proof.X25519.Arm.val16 f n < 2 ^ (16 * n)
  | 0, _ => Nat.one_pos
  | n + 1, h => by
    have ih := VG.Proof.X25519.Arm.val16_lt (n := n) fun k hk => h k (by omega)
    have h1 : 2 ^ (16 * n) * f n ≤ 2 ^ (16 * n) * 65535 :=
      Nat.mul_le_mul_left _ (by have := h n (by omega); omega)
    rw [VG.Proof.X25519.Arm.val16_succ, VG.Proof.X25519.Arm.pow16_succ]
    omega

theorem val16_add (f g : Nat → Nat) :
    ∀ n, VG.Proof.X25519.Arm.val16 (fun k => f k + g k) n = VG.Proof.X25519.Arm.val16 f n + VG.Proof.X25519.Arm.val16 g n
  | 0 => rfl
  | n + 1 => by rw [VG.Proof.X25519.Arm.val16_succ, VG.Proof.X25519.Arm.val16_succ, VG.Proof.X25519.Arm.val16_succ, VG.Proof.X25519.Arm.val16_add f g n, Nat.mul_add]; omega

theorem val16_cmul (a : Nat) (f : Nat → Nat) : ∀ n, VG.Proof.X25519.Arm.val16 (fun k => a * f k) n = a * VG.Proof.X25519.Arm.val16 f n
  | 0 => rfl
  | n + 1 => by
    rw [VG.Proof.X25519.Arm.val16_succ, VG.Proof.X25519.Arm.val16_succ, VG.Proof.X25519.Arm.val16_cmul a f n, Nat.mul_add, Nat.mul_left_comm]

theorem val16_append (f : Nat → Nat) (m : Nat) :
    ∀ n, VG.Proof.X25519.Arm.val16 f (m + n) = VG.Proof.X25519.Arm.val16 f m + 2 ^ (16 * m) * VG.Proof.X25519.Arm.val16 (fun k => f (m + k)) n
  | 0 => by simp [VG.Proof.X25519.Arm.val16]
  | n + 1 => by
    rw [← Nat.add_assoc, VG.Proof.X25519.Arm.val16_succ, VG.Proof.X25519.Arm.val16_append f m n, VG.Proof.X25519.Arm.val16_succ, Nat.mul_add (2 ^ (16 * m)),
      ← Nat.mul_assoc, ← Nat.pow_add, Nat.mul_add 16 m n]
    omega

theorem val16_zero_fn : ∀ n, VG.Proof.X25519.Arm.val16 (fun _ => 0) n = 0
  | 0 => rfl
  | n + 1 => by rw [VG.Proof.X25519.Arm.val16_succ, VG.Proof.X25519.Arm.val16_zero_fn n]; rfl

theorem val16_mono (f : Nat → Nat) {m n : Nat} (h : m ≤ n) : VG.Proof.X25519.Arm.val16 f m ≤ VG.Proof.X25519.Arm.val16 f n := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [VG.Proof.X25519.Arm.val16_append]; exact Nat.le_add_right _ _

theorem val16_head (f : Nat → Nat) {n : Nat} (hn : 0 < n) : f 0 ≤ VG.Proof.X25519.Arm.val16 f n := by
  have := VG.Proof.X25519.Arm.val16_mono f (m := 1) (n := n) hn
  simp only [VG.Proof.X25519.Arm.val16] at this
  omega

/-- Changing limb 0 by `d`. -/
theorem val16_add_head (f : Nat → Nat) (d : Nat) {n : Nat} (hn : 0 < n) :
    VG.Proof.X25519.Arm.val16 (fun k => if k = 0 then f 0 + d else f k) n = VG.Proof.X25519.Arm.val16 f n + d := by
  have e : VG.Proof.X25519.Arm.val16 (fun k => if k = 0 then f 0 + d else f k) n =
      VG.Proof.X25519.Arm.val16 (fun k => f k + if k = 0 then d else 0) n :=
    VG.Proof.X25519.Arm.val16_congr fun k _ => by by_cases h : k = 0 <;> simp [h]
  rw [e, VG.Proof.X25519.Arm.val16_add]
  congr 1
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  rw [Nat.add_comm, VG.Proof.X25519.Arm.val16_append, show VG.Proof.X25519.Arm.val16 (fun k => if k = 0 then d else 0) 1 = d by simp [VG.Proof.X25519.Arm.val16]]
  rw [VG.Proof.X25519.Arm.val16_congr (g := fun _ => 0) (fun k _ => by simp), VG.Proof.X25519.Arm.val16_zero_fn, Nat.mul_zero, Nat.add_zero]

/-! ## Carrying -/

/-- The carry into limb `k` of the limbs of `Σ c k 2^(16k) + cin`. -/
def chain (c : Nat → Nat) (cin : Nat) : Nat → Nat
  | 0 => cin
  | k + 1 => (c k + VG.Proof.X25519.Arm.chain c cin k) / 65536

/-- Limb `k` of the limbs of `Σ c k 2^(16k) + cin`. -/
def out (c : Nat → Nat) (cin k : Nat) : Nat := (c k + VG.Proof.X25519.Arm.chain c cin k) % 65536

theorem chain_succ (c : Nat → Nat) (cin k : Nat) :
    VG.Proof.X25519.Arm.chain c cin (k + 1) = (c k + VG.Proof.X25519.Arm.chain c cin k) / 65536 := rfl

theorem out_lt (c : Nat → Nat) (cin k : Nat) : VG.Proof.X25519.Arm.out c cin k < 65536 := Nat.mod_lt _ (by decide)

theorem chain_val (c : Nat → Nat) (cin : Nat) :
    ∀ n, VG.Proof.X25519.Arm.val16 (VG.Proof.X25519.Arm.out c cin) n + 2 ^ (16 * n) * VG.Proof.X25519.Arm.chain c cin n = VG.Proof.X25519.Arm.val16 c n + cin
  | 0 => by simp [VG.Proof.X25519.Arm.val16, VG.Proof.X25519.Arm.chain]
  | n + 1 => by
    have ih := VG.Proof.X25519.Arm.chain_val c cin n
    rw [VG.Proof.X25519.Arm.val16_succ, VG.Proof.X25519.Arm.val16_succ, VG.Proof.X25519.Arm.chain_succ, VG.Proof.X25519.Arm.pow16_succ, VG.Proof.X25519.Arm.out]
    have e : 2 ^ (16 * n) * ((c n + VG.Proof.X25519.Arm.chain c cin n) % 65536) +
        2 ^ (16 * n) * 65536 * ((c n + VG.Proof.X25519.Arm.chain c cin n) / 65536) = 2 ^ (16 * n) * (c n + VG.Proof.X25519.Arm.chain c cin n) := by
      rw [Nat.mul_assoc, ← Nat.mul_add, Nat.mod_add_div]
    rw [Nat.mul_add] at e
    omega

/-- The carries stay below `2¹⁶` (and each sum below `2³²`) if every sum is at
most `2³² - 2¹⁶`. -/
theorem chain_lt {c : Nat → Nat} {cin n : Nat} (hc : ∀ k < n, c k + 65536 ≤ 2 ^ 32)
    (hcin : cin < 65536) : ∀ k ≤ n, VG.Proof.X25519.Arm.chain c cin k < 65536
  | 0, _ => hcin
  | k + 1, hk => by
    have := VG.Proof.X25519.Arm.chain_lt hc hcin k (by omega)
    have := hc k (by omega)
    rw [VG.Proof.X25519.Arm.chain_succ, Nat.div_lt_iff_lt_mul (by decide)]
    omega

theorem sum_lt {c : Nat → Nat} {cin n : Nat} (hc : ∀ k < n, c k + 65536 ≤ 2 ^ 32)
    (hcin : cin < 65536) {k : Nat} (hk : k < n) : c k + VG.Proof.X25519.Arm.chain c cin k < 2 ^ 32 := by
  have := VG.Proof.X25519.Arm.chain_lt hc hcin k (by omega)
  have := hc k hk
  omega

/-! ## A row of a product -/

/-- Row `i` of a product: the sums `a_i b_j + acc_(i+j)`. -/
def rowC (acc a b : Nat → Nat) (i j : Nat) : Nat := a i * b j + acc (i + j)

/-- The limbs after row `i`: those below `i`, the row's limbs, and its carry. -/
def rowAcc (acc a b : Nat → Nat) (i k : Nat) : Nat :=
  if k < i then acc k else if k < i + 16 then VG.Proof.X25519.Arm.out (VG.Proof.X25519.Arm.rowC acc a b i) 0 (k - i)
  else VG.Proof.X25519.Arm.chain (VG.Proof.X25519.Arm.rowC acc a b i) 0 16

theorem row_val {acc a b : Nat → Nat} {i : Nat} (hv : VG.Proof.X25519.Arm.val16 acc (i + 16) = VG.Proof.X25519.Arm.val16 a i * VG.Proof.X25519.Arm.val16 b 16) :
    VG.Proof.X25519.Arm.val16 (VG.Proof.X25519.Arm.rowAcc acc a b i) (i + 17) = VG.Proof.X25519.Arm.val16 a (i + 1) * VG.Proof.X25519.Arm.val16 b 16 := by
  have e1 : VG.Proof.X25519.Arm.val16 (VG.Proof.X25519.Arm.rowAcc acc a b i) i = VG.Proof.X25519.Arm.val16 acc i :=
    VG.Proof.X25519.Arm.val16_congr fun k hk => by simp [VG.Proof.X25519.Arm.rowAcc, hk]
  have e2 : VG.Proof.X25519.Arm.val16 (fun k => VG.Proof.X25519.Arm.rowAcc acc a b i (i + k)) 17 =
      VG.Proof.X25519.Arm.val16 (VG.Proof.X25519.Arm.out (VG.Proof.X25519.Arm.rowC acc a b i) 0) 16 + 2 ^ 256 * VG.Proof.X25519.Arm.chain (VG.Proof.X25519.Arm.rowC acc a b i) 0 16 := by
    rw [VG.Proof.X25519.Arm.val16_succ, VG.Proof.X25519.Arm.val16_congr (g := VG.Proof.X25519.Arm.out (VG.Proof.X25519.Arm.rowC acc a b i) 0) fun k hk => by
      simp only [VG.Proof.X25519.Arm.rowAcc, show ¬ i + k < i by omega, show i + k < i + 16 by omega, ite_false, ite_true,
        Nat.add_sub_cancel_left]]
    simp only [VG.Proof.X25519.Arm.rowAcc, show ¬ i + 16 < i by omega, Nat.lt_irrefl, ite_false]
  have e3 : VG.Proof.X25519.Arm.val16 (VG.Proof.X25519.Arm.rowC acc a b i) 16 = a i * VG.Proof.X25519.Arm.val16 b 16 + VG.Proof.X25519.Arm.val16 (fun k => acc (i + k)) 16 := by
    rw [← VG.Proof.X25519.Arm.val16_cmul, ← VG.Proof.X25519.Arm.val16_add]; rfl
  have hc := VG.Proof.X25519.Arm.chain_val (VG.Proof.X25519.Arm.rowC acc a b i) 0 16
  rw [show 16 * 16 = 256 from rfl, Nat.add_zero, e3] at hc
  rw [VG.Proof.X25519.Arm.val16_append _ i 17, e1, e2, hc, VG.Proof.X25519.Arm.val16_succ a i, Nat.add_mul, ← hv, VG.Proof.X25519.Arm.val16_append acc i 16,
    Nat.mul_add, Nat.mul_assoc]
  omega

theorem rowC_le {acc a b : Nat → Nat} {i j : Nat} (ha : a i < 65536) (hb : b j < 65536)
    (hacc : acc (i + j) < 65536) : VG.Proof.X25519.Arm.rowC acc a b i j + 65536 ≤ 2 ^ 32 := by
  simp only [VG.Proof.X25519.Arm.rowC]
  have : a i * b j ≤ 65535 * 65535 := Nat.mul_le_mul (by omega) (by omega)
  omega

theorem rowAcc_lt {acc a b : Nat → Nat} {i : Nat} (hacc : ∀ k < i, acc k < 65536)
    (hc : ∀ j < 16, VG.Proof.X25519.Arm.rowC acc a b i j + 65536 ≤ 2 ^ 32) :
    ∀ k < i + 17, VG.Proof.X25519.Arm.rowAcc acc a b i k < 65536 := by
  intro k _
  simp only [VG.Proof.X25519.Arm.rowAcc]
  split
  · exact hacc k (by omega)
  · split
    · exact VG.Proof.X25519.Arm.out_lt _ _ _
    · exact VG.Proof.X25519.Arm.chain_lt hc (by decide) 16 (Nat.le_refl _)

/-! ## The fold of a product and the tail -/

/-- The sums `lo_k + 38 hi_k` of a product's limbs. -/
def foldC (acc : Nat → Nat) (k : Nat) : Nat := acc k + 38 * acc (16 + k)

theorem foldC_le {acc : Nat → Nat} (h : ∀ k < 32, acc k < 65536) :
    ∀ k < 16, VG.Proof.X25519.Arm.foldC acc k + 65536 ≤ 2 ^ 32 := by
  intro k hk
  have := h k (by omega)
  have := h (16 + k) (by omega)
  simp only [VG.Proof.X25519.Arm.foldC]
  omega

theorem val16_foldC (acc : Nat → Nat) :
    VG.Proof.X25519.Arm.val16 (VG.Proof.X25519.Arm.foldC acc) 16 = VG.Proof.X25519.Arm.val16 acc 16 + 38 * VG.Proof.X25519.Arm.val16 (fun k => acc (16 + k)) 16 := by
  rw [← VG.Proof.X25519.Arm.val16_cmul, ← VG.Proof.X25519.Arm.val16_add]; rfl

theorem fold_facts {acc : Nat → Nat} (h : ∀ k < 32, acc k < 65536) :
    VG.Proof.X25519.Arm.chain (VG.Proof.X25519.Arm.foldC acc) 0 16 ≤ 38 ∧
      (VG.Proof.X25519.Arm.val16 (VG.Proof.X25519.Arm.out (VG.Proof.X25519.Arm.foldC acc) 0) 16 + 2 ^ 256 * VG.Proof.X25519.Arm.chain (VG.Proof.X25519.Arm.foldC acc) 0 16) % P = VG.Proof.X25519.Arm.val16 acc 32 % P := by
  have hc := VG.Proof.X25519.Arm.chain_val (VG.Proof.X25519.Arm.foldC acc) 0 16
  have hs := VG.Proof.X25519.Arm.val16_append acc 16 16
  have hlo := VG.Proof.X25519.Arm.val16_lt (f := acc) (n := 16) fun k hk => h k (by omega)
  have hhi := VG.Proof.X25519.Arm.val16_lt (f := fun k => acc (16 + k)) (n := 16) fun k hk => h (16 + k) (by omega)
  rw [VG.Proof.X25519.Arm.val16_foldC] at hc
  rw [show 16 * 16 = 256 from rfl] at hc hlo hhi hs
  refine ⟨?_, ?_⟩
  · have : 2 ^ 256 * VG.Proof.X25519.Arm.chain (VG.Proof.X25519.Arm.foldC acc) 0 16 < 2 ^ 256 * 39 := by omega
    have := Nat.lt_of_mul_lt_mul_left this
    omega
  · rw [show (16 : Nat) + 16 = 32 from rfl] at hs
    rw [hc, Nat.add_zero, hs, fold256]

/-- The final limbs of `tail`: limb 0 plus 38 times the carry out. -/
def tailL (l : Nat → Nat) (c16 k : Nat) : Nat :=
  if k = 0 then VG.Proof.X25519.Arm.out l (38 * c16) 0 + 38 * VG.Proof.X25519.Arm.chain l (38 * c16) 16 else VG.Proof.X25519.Arm.out l (38 * c16) k

theorem tail_facts {l : Nat → Nat} (hl : ∀ k < 16, l k < 65536) {c16 : Nat} (hc : c16 ≤ 38) :
    VG.Proof.X25519.Arm.chain l (38 * c16) 16 ≤ 1 ∧ (∀ k < 16, VG.Proof.X25519.Arm.tailL l c16 k < 65536) ∧
      VG.Proof.X25519.Arm.val16 (VG.Proof.X25519.Arm.tailL l c16) 16 % P = (VG.Proof.X25519.Arm.val16 l 16 + 2 ^ 256 * c16) % P := by
  have hv := VG.Proof.X25519.Arm.chain_val l (38 * c16) 16
  have hL := VG.Proof.X25519.Arm.val16_lt (f := l) (n := 16) hl
  have hO := VG.Proof.X25519.Arm.val16_lt (f := VG.Proof.X25519.Arm.out l (38 * c16)) (n := 16) fun k _ => VG.Proof.X25519.Arm.out_lt _ _ _
  have h0 := VG.Proof.X25519.Arm.val16_head (VG.Proof.X25519.Arm.out l (38 * c16)) (n := 16) (by decide)
  rw [show 16 * 16 = 256 from rfl] at hv hL hO
  have ht : VG.Proof.X25519.Arm.chain l (38 * c16) 16 ≤ 1 := by
    have : 2 ^ 256 * VG.Proof.X25519.Arm.chain l (38 * c16) 16 < 2 ^ 256 * 2 := by omega
    have := Nat.lt_of_mul_lt_mul_left this
    omega
  refine ⟨ht, fun k hk => ?_, ?_⟩
  · simp only [VG.Proof.X25519.Arm.tailL]
    split
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ht with h | h
      · rw [h]; exact VG.Proof.X25519.Arm.out_lt _ _ _
      · rw [h] at hv ⊢; omega
    · exact VG.Proof.X25519.Arm.out_lt _ _ _
  · have e : VG.Proof.X25519.Arm.val16 (VG.Proof.X25519.Arm.tailL l c16) 16 = VG.Proof.X25519.Arm.val16 (VG.Proof.X25519.Arm.out l (38 * c16)) 16 + 38 * VG.Proof.X25519.Arm.chain l (38 * c16) 16 :=
      VG.Proof.X25519.Arm.val16_add_head (VG.Proof.X25519.Arm.out l (38 * c16)) _ (by decide)
    rw [e, ← fold256, hv, fold256]

/-! ## Sums and differences -/

/-- Limb `k` of `4p`. -/
def fourP (k : Nat) : Nat := if k = 0 then 262068 else if k = 15 then 131068 else 262140

theorem val16_fourP : VG.Proof.X25519.Arm.val16 VG.Proof.X25519.Arm.fourP 16 = 4 * P := by decide

theorem fourP_ge : ∀ k < 16, 65535 ≤ VG.Proof.X25519.Arm.fourP k := by decide

theorem fourP_le : ∀ k < 16, VG.Proof.X25519.Arm.fourP k ≤ 262140 := by decide

/-- The sums of a difference: `a_k + 4p_k - b_k`. -/
def subC (a b : Nat → Nat) (k : Nat) : Nat := a k + VG.Proof.X25519.Arm.fourP k - b k

theorem subC_facts {a b : Nat → Nat} (ha : ∀ k < 16, a k < 65536) (hb : ∀ k < 16, b k < 65536) :
    (∀ k < 16, VG.Proof.X25519.Arm.subC a b k + 65536 ≤ 2 ^ 32) ∧ VG.Proof.X25519.Arm.val16 (VG.Proof.X25519.Arm.subC a b) 16 + VG.Proof.X25519.Arm.val16 b 16 = VG.Proof.X25519.Arm.val16 a 16 + 4 * P := by
  have hK := VG.Proof.X25519.Arm.fourP_ge
  refine ⟨fun k hk => ?_, ?_⟩
  · have := ha k hk; have := hb k hk
    have := VG.Proof.X25519.Arm.fourP_le k hk
    simp only [VG.Proof.X25519.Arm.subC]; omega
  · rw [← VG.Proof.X25519.Arm.val16_add, ← VG.Proof.X25519.Arm.val16_fourP, ← VG.Proof.X25519.Arm.val16_add]
    exact VG.Proof.X25519.Arm.val16_congr fun k hk => by have := hK k hk; have := hb k hk; simp only [VG.Proof.X25519.Arm.subC]; omega

/-- The carry out of the limbs of a sum or difference of numbers below
`2²⁵⁶` is at most 38 (it is at most 2). -/
theorem carry_le {c : Nat → Nat} (h : VG.Proof.X25519.Arm.val16 c 16 < 39 * 2 ^ 256) : VG.Proof.X25519.Arm.chain c 0 16 ≤ 38 := by
  have hv := VG.Proof.X25519.Arm.chain_val c 0 16
  rw [show 16 * 16 = 256 from rfl] at hv
  have : 2 ^ 256 * VG.Proof.X25519.Arm.chain c 0 16 < 2 ^ 256 * 39 := by omega
  have := Nat.lt_of_mul_lt_mul_left this
  omega

/-! ## The final reduction -/

/-- `c` if `sw = 1`, else `a`. -/
def sel {α : Type} (sw : Nat) (a c : α) : α := if sw = 1 then c else a

/-- Limb 15 cut to 15 bits: the number modulo `2²⁵⁵`. -/
def mask15 (l : Nat → Nat) (k : Nat) : Nat := if k = 15 then l 15 % 32768 else l k

theorem mask15_facts {l : Nat → Nat} (hl : ∀ k < 16, l k < 65536) :
    VG.Proof.X25519.Arm.val16 l 16 = VG.Proof.X25519.Arm.val16 (VG.Proof.X25519.Arm.mask15 l) 16 + 2 ^ 255 * (l 15 / 32768) ∧ VG.Proof.X25519.Arm.val16 (VG.Proof.X25519.Arm.mask15 l) 16 < 2 ^ 255 ∧
      (∀ k < 16, VG.Proof.X25519.Arm.mask15 l k < 65536) ∧ l 15 / 32768 ≤ 1 := by
  have e : VG.Proof.X25519.Arm.val16 (VG.Proof.X25519.Arm.mask15 l) 15 = VG.Proof.X25519.Arm.val16 l 15 := VG.Proof.X25519.Arm.val16_congr fun k hk => by simp [VG.Proof.X25519.Arm.mask15, show k ≠ 15 by omega]
  have h15 := hl 15 (by decide)
  have hlo := VG.Proof.X25519.Arm.val16_lt (f := l) (n := 15) fun k hk => hl k (by omega)
  rw [show 16 * 15 = 240 from rfl] at hlo
  have hm : l 15 = l 15 % 32768 + 32768 * (l 15 / 32768) := (Nat.mod_add_div _ _).symm
  refine ⟨?_, ?_, fun k hk => ?_, by omega⟩
  · rw [VG.Proof.X25519.Arm.val16_succ l 15, VG.Proof.X25519.Arm.val16_succ (VG.Proof.X25519.Arm.mask15 l) 15, e, show VG.Proof.X25519.Arm.mask15 l 15 = l 15 % 32768 from rfl,
      show 16 * 15 = 240 from rfl]
    conv => lhs; rw [hm]
    rw [Nat.mul_add, show (2 : Nat) ^ 255 = 2 ^ 240 * 32768 from rfl, Nat.mul_assoc]; omega
  · rw [VG.Proof.X25519.Arm.val16_succ (VG.Proof.X25519.Arm.mask15 l) 15, e, show VG.Proof.X25519.Arm.mask15 l 15 = l 15 % 32768 from rfl, show 16 * 15 = 240 from rfl]
    have : 2 ^ 240 * (l 15 % 32768) ≤ 2 ^ 240 * 32767 :=
      Nat.mul_le_mul_left _ (by have := Nat.mod_lt (l 15) (show 32768 > 0 by decide); omega)
    rw [show (2 : Nat) ^ 255 = 2 ^ 240 * 32768 from rfl]; omega
  · simp only [VG.Proof.X25519.Arm.mask15]; split
    · exact Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)
    · exact hl k hk

/-- The limbs of `x' = x mod 2²⁵⁵ + 19 (x >> 255)`. -/
def frA (l : Nat → Nat) : Nat → Nat := VG.Proof.X25519.Arm.out (VG.Proof.X25519.Arm.mask15 l) (19 * (l 15 / 32768))

/-- The limbs of `x' + 19`. -/
def frY (l : Nat → Nat) : Nat → Nat := VG.Proof.X25519.Arm.out (VG.Proof.X25519.Arm.frA l) 19

/-- Whether `x' + 19 ≥ 2²⁵⁵`, that is `x' ≥ p`. -/
def frS (l : Nat → Nat) : Nat := VG.Proof.X25519.Arm.frY l 15 / 32768

/-- The limbs of `x mod p`. -/
def frR (l : Nat → Nat) (k : Nat) : Nat := VG.Proof.X25519.Arm.sel (VG.Proof.X25519.Arm.frS l) (VG.Proof.X25519.Arm.frA l k) (VG.Proof.X25519.Arm.mask15 (VG.Proof.X25519.Arm.frY l) k)

theorem freeze_facts {l : Nat → Nat} (hl : ∀ k < 16, l k < 65536) :
    VG.Proof.X25519.Arm.chain (VG.Proof.X25519.Arm.mask15 l) (19 * (l 15 / 32768)) 16 = 0 ∧ VG.Proof.X25519.Arm.chain (VG.Proof.X25519.Arm.frA l) 19 16 = 0 ∧ VG.Proof.X25519.Arm.frS l ≤ 1 ∧
      (∀ k < 16, VG.Proof.X25519.Arm.frR l k < 65536) ∧ VG.Proof.X25519.Arm.val16 (VG.Proof.X25519.Arm.frR l) 16 = VG.Proof.X25519.Arm.val16 l 16 % P := by
  obtain ⟨e1, b1, lm, c1⟩ := VG.Proof.X25519.Arm.mask15_facts hl
  have hA := VG.Proof.X25519.Arm.chain_val (VG.Proof.X25519.Arm.mask15 l) (19 * (l 15 / 32768)) 16
  rw [show 16 * 16 = 256 from rfl] at hA
  have tA : VG.Proof.X25519.Arm.chain (VG.Proof.X25519.Arm.mask15 l) (19 * (l 15 / 32768)) 16 = 0 := by
    rcases Nat.eq_zero_or_pos (VG.Proof.X25519.Arm.chain (VG.Proof.X25519.Arm.mask15 l) (19 * (l 15 / 32768)) 16) with h | h
    · exact h
    · have : 2 ^ 256 ≤ 2 ^ 256 * VG.Proof.X25519.Arm.chain (VG.Proof.X25519.Arm.mask15 l) (19 * (l 15 / 32768)) 16 := Nat.le_mul_of_pos_right _ h
      omega
  rw [tA, Nat.mul_zero, Nat.add_zero] at hA
  -- `x' = val16 (frA l) 16`.
  have hY := VG.Proof.X25519.Arm.chain_val (VG.Proof.X25519.Arm.frA l) 19 16
  rw [show 16 * 16 = 256 from rfl] at hY
  have hAl : ∀ k < 16, VG.Proof.X25519.Arm.frA l k < 65536 := fun k _ => VG.Proof.X25519.Arm.out_lt _ _ _
  have hYl : ∀ k < 16, VG.Proof.X25519.Arm.frY l k < 65536 := fun k _ => VG.Proof.X25519.Arm.out_lt _ _ _
  have tY : VG.Proof.X25519.Arm.chain (VG.Proof.X25519.Arm.frA l) 19 16 = 0 := by
    rcases Nat.eq_zero_or_pos (VG.Proof.X25519.Arm.chain (VG.Proof.X25519.Arm.frA l) 19 16) with h | h
    · exact h
    · have : 2 ^ 256 ≤ 2 ^ 256 * VG.Proof.X25519.Arm.chain (VG.Proof.X25519.Arm.frA l) 19 16 := Nat.le_mul_of_pos_right _ h
      have : VG.Proof.X25519.Arm.val16 (VG.Proof.X25519.Arm.frA l) 16 = VG.Proof.X25519.Arm.val16 (VG.Proof.X25519.Arm.mask15 l) 16 + 19 * (l 15 / 32768) := hA
      omega
  rw [tY, Nat.mul_zero, Nat.add_zero] at hY
  obtain ⟨e2, b2, lm2, c2⟩ := VG.Proof.X25519.Arm.mask15_facts hYl
  have hxA : VG.Proof.X25519.Arm.val16 (VG.Proof.X25519.Arm.frA l) 16 = VG.Proof.X25519.Arm.val16 (VG.Proof.X25519.Arm.mask15 l) 16 + 19 * (l 15 / 32768) := hA
  have hyv : VG.Proof.X25519.Arm.val16 (VG.Proof.X25519.Arm.frY l) 16 = VG.Proof.X25519.Arm.val16 (VG.Proof.X25519.Arm.frA l) 16 + 19 := hY
  have hP : P = 2 ^ 255 - 19 := rfl
  have hx : VG.Proof.X25519.Arm.val16 l 16 % P = VG.Proof.X25519.Arm.val16 (VG.Proof.X25519.Arm.frA l) 16 % P := by
    rw [e1, hxA, fold255]
  refine ⟨tA, tY, c2, fun k hk => ?_, ?_⟩
  · simp only [VG.Proof.X25519.Arm.frR, VG.Proof.X25519.Arm.sel]; split
    · exact lm2 k hk
    · exact hAl k hk
  · rw [hx]
    have hs : VG.Proof.X25519.Arm.frS l = VG.Proof.X25519.Arm.frY l 15 / 32768 := rfl
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp c2 with h0 | h1
    · have e : VG.Proof.X25519.Arm.val16 (VG.Proof.X25519.Arm.frR l) 16 = VG.Proof.X25519.Arm.val16 (VG.Proof.X25519.Arm.frA l) 16 :=
        VG.Proof.X25519.Arm.val16_congr fun k _ => by simp only [VG.Proof.X25519.Arm.frR, VG.Proof.X25519.Arm.sel, hs, h0]; rfl
      rw [e, Nat.mod_eq_of_lt (by rw [h0] at e2; omega)]
    · have e : VG.Proof.X25519.Arm.val16 (VG.Proof.X25519.Arm.frR l) 16 = VG.Proof.X25519.Arm.val16 (VG.Proof.X25519.Arm.mask15 (VG.Proof.X25519.Arm.frY l)) 16 :=
        VG.Proof.X25519.Arm.val16_congr fun k _ => by simp only [VG.Proof.X25519.Arm.frR, VG.Proof.X25519.Arm.sel, hs, h1, ite_true]
      rw [e]
      rw [h1] at e2
      have : VG.Proof.X25519.Arm.val16 (VG.Proof.X25519.Arm.frA l) 16 = VG.Proof.X25519.Arm.val16 (VG.Proof.X25519.Arm.mask15 (VG.Proof.X25519.Arm.frY l)) 16 + P := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-- The limbs of a number of 16 limbs below `2¹⁶`. -/
theorem val16_div {r : Nat → Nat} {n : Nat} (hr : ∀ k < n, r k < 65536) {k : Nat} (hk : k < n) :
    VG.Proof.X25519.Arm.val16 r n / 2 ^ (16 * k) % 65536 = r k := by
  have e := VG.Proof.X25519.Arm.val16_append r k (n - k)
  rw [Nat.add_sub_cancel' (by omega)] at e
  have e' := VG.Proof.X25519.Arm.val16_append (fun j => r (k + j)) 1 (n - k - 1)
  rw [Nat.add_sub_cancel' (by omega)] at e'
  simp only [VG.Proof.X25519.Arm.val16, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.add_zero] at e'
  have hlt := VG.Proof.X25519.Arm.val16_lt (f := r) (n := k) fun j hj => hr j (by omega)
  rw [e, e', Nat.mul_comm (2 ^ (16 * k)), Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
    Nat.div_eq_of_lt hlt, Nat.zero_add, show (2 : Nat) ^ (16 * 1) = 65536 from rfl, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (hr k hk)]

/-- The bytes of a number of 16 limbs below `2¹⁶`. -/
theorem bytes_of_limbs {r : Nat → Nat} (hr : ∀ k < 16, r k < 65536) {k : Nat} (hk : k < 16) :
    VG.Proof.X25519.Arm.val16 r 16 / 256 ^ (2 * k) % 256 = r k % 256 ∧ VG.Proof.X25519.Arm.val16 r 16 / 256 ^ (2 * k + 1) % 256 = r k / 256 := by
  have h := VG.Proof.X25519.Arm.val16_div hr hk
  have p1 : (256 : Nat) ^ (2 * k) = 2 ^ (16 * k) := by
    rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]; congr 1; omega
  refine ⟨?_, ?_⟩
  · rw [p1, ← h, Nat.mod_mod_of_dvd _ (by decide)]
  · rw [Nat.pow_succ, p1, ← Nat.div_div_eq_div_mul, ← h, show (65536 : Nat) = 256 * 256 from rfl,
      Nat.mod_mul_right_div_self]

end VG.Proof.X25519.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.Arm.Instr`. -/
section

/-!
# X25519 on 32-bit ARM: one instruction at a time

WP rules for the instructions the code uses, which expose only what changes
(`Upd`: one register, `Mupd`: the memory), what a piece of code leaves
unchanged (`Rest`), words of memory at offsets from a base (`wd`), and 32-bit
arithmetic without overflow.
-/

namespace VG.Proof.X25519.Arm

open VG VG.Arm

/-! ## What code changes -/

/-- `s'` is `s` except for the registers `ws`, the flags and the memory. -/
structure Rest (ws : List Reg) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ ws → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Rest.refl (ws : List Reg) (s : State) : VG.Proof.X25519.Arm.Rest ws s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem Rest.trans {ws : List Reg} {s₁ s₂ s₃ : State} (h₁ : VG.Proof.X25519.Arm.Rest ws s₁ s₂) (h₂ : VG.Proof.X25519.Arm.Rest ws s₂ s₃) :
    VG.Proof.X25519.Arm.Rest ws s₁ s₃ :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr,
    h₂.sp.trans h₁.sp⟩

theorem Rest.mono {ws ws' : List Reg} {s s' : State} (h : VG.Proof.X25519.Arm.Rest ws s s') (hs : ∀ r ∈ ws, r ∈ ws') :
    VG.Proof.X25519.Arm.Rest ws' s s' :=
  ⟨fun r hr => h.gpr r fun h' => hr (hs r h'), h.rd, h.wr, h.sp⟩

/-- `s'` is `s` with register `d` set to `v` (the flags aside). -/
structure Upd (s s' : State) (d : Reg) (v : BitVec 32) : Prop where
  gpr : s'.gpr d = v
  other : ∀ r, r ≠ d → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Upd.setReg (s : State) (d : Reg) (v : BitVec 32) : VG.Proof.X25519.Arm.Upd s (s.setReg d v) d v :=
  ⟨by simp only [State.setReg, ↓reduceIte], fun r h => by simp only [State.setReg, h, ↓reduceIte],
    rfl, rfl, rfl, rfl⟩

theorem Upd.subs (s : State) (d : Reg) (x y v : BitVec 32) :
    VG.Proof.X25519.Arm.Upd s ((subFlags s x y).setReg d v) d v :=
  ⟨by simp only [State.setReg, ↓reduceIte],
    fun r h => by simp only [State.setReg, subFlags, h, ↓reduceIte], rfl, rfl, rfl, rfl⟩

theorem Upd.rest {s s' : State} {d : Reg} {v : BitVec 32} (h : VG.Proof.X25519.Arm.Upd s s' d v) {ws : List Reg}
    (hd : d ∈ ws) : VG.Proof.X25519.Arm.Rest ws s s' :=
  ⟨fun r hr => h.other r fun e => hr (e ▸ hd), h.rd, h.wr, h.sp⟩

/-- `s'` is `s` with memory `m`. -/
structure Mupd (s s' : State) (m : Mem) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = m
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Mupd.rest {s s' : State} {m : Mem} (h : VG.Proof.X25519.Arm.Mupd s s' m) (ws : List Reg) : VG.Proof.X25519.Arm.Rest ws s s' :=
  ⟨fun r _ => by rw [h.gpr], h.rd, h.wr, h.sp⟩

/-- `s'` is `s` with other flags. -/
structure Fupd (s s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Fupd.rest {s s' : State} (h : VG.Proof.X25519.Arm.Fupd s s') (ws : List Reg) : VG.Proof.X25519.Arm.Rest ws s s' :=
  ⟨fun r _ => by rw [h.gpr], h.rd, h.wr, h.sp⟩

/-! ## One instruction at a time -/

theorem WP.cons {i : Instr} {is : List Instr} {s s' : State} {Q : State → Prop}
    (h : exec i s = some s') (k : WP isa (.block is) s' Q) : WP isa (.block (i :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨s', h, k⟩

theorem op2_imm {s : State} {v : BitVec 32} (h : encodable v = true) : (Op2.imm v).eval s = some v := by
  simp only [Op2.eval, h, ↓reduceIte]

theorem op2_reg (s : State) (r : Reg) : (Op2.reg r).eval s = some (s.gpr r) := rfl

theorem op2_lsr {s : State} {r : Reg} {n : Nat} (h : 1 ≤ n ∧ n ≤ 31) :
    (Op2.shifted r .lsr n).eval s = some (s.gpr r >>> n) := by
  simp only [Op2.eval, h, and_self, ↓reduceIte]

theorem op2_lsl {s : State} {r : Reg} {n : Nat} (h : 1 ≤ n ∧ n ≤ 31) :
    (Op2.shifted r .lsl n).eval s = some (s.gpr r <<< n) := by
  simp only [Op2.eval, h, and_self, ↓reduceIte]

/-- The value of a data-processing instruction. -/
def dpVal (op : DpOp) (x y : BitVec 32) : BitVec 32 :=
  match op with
  | .add => x + y | .sub => x - y | .and => x &&& y | .orr => x ||| y | .eor => x ^^^ y

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_mov {d : Reg} {o : Op2} {v : BitVec 32} (ho : o.eval s = some v)
    (k : ∀ s', VG.Proof.X25519.Arm.Upd s s' d v → WP isa (.block is) s' Q) : WP isa (.block (.mov d o :: is)) s Q :=
  WP.cons (s' := s.setReg d v) (by simp only [exec, ho, Option.map_some]) (k _ (Upd.setReg _ _ _))

theorem wp_dp {op : DpOp} {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', VG.Proof.X25519.Arm.Upd s s' d (VG.Proof.X25519.Arm.dpVal op (s.gpr n) y) → WP isa (.block is) s' Q) :
    WP isa (.block (.dp op d n o :: is)) s Q :=
  WP.cons (s' := s.setReg d (VG.Proof.X25519.Arm.dpVal op (s.gpr n) y))
    (by cases op <;> simp only [exec, ho, Option.map_some, VG.Proof.X25519.Arm.dpVal]) (k _ (Upd.setReg _ _ _))

theorem wp_mul {d n m : Reg} (k : ∀ s', VG.Proof.X25519.Arm.Upd s s' d (s.gpr n * s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.mul d n m :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

theorem wp_movw {d : Reg} {imm : BitVec 16}
    (k : ∀ s', VG.Proof.X25519.Arm.Upd s s' d (imm.setWidth 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movw d imm :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

theorem wp_subs {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', VG.Proof.X25519.Arm.Upd s s' d (s.gpr n - y) → s'.z = (s.gpr n - y == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.subs d n o :: is)) s Q :=
  WP.cons (s' := (subFlags s (s.gpr n) y).setReg d (s.gpr n - y)) (by simp only [exec, ho, Option.map_some])
    (k _ (Upd.subs _ _ _ _ _) rfl)

theorem wp_cmp {n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', VG.Proof.X25519.Arm.Fupd s s' → s'.z = (s.gpr n - y == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.cmp n o :: is)) s Q :=
  WP.cons (s' := subFlags s (s.gpr n) y) (by simp only [exec, ho, Option.map_some])
    (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl)

theorem wp_ldr {t n : Reg} {off : Nat} {a : Addr} (ho : off < 4096)
    (ha : State.addr (s.gpr n + BitVec.ofNat 32 off) = a) (hin : InRegions (s.rd ++ s.wr) a 4)
    (k : ∀ s', VG.Proof.X25519.Arm.Upd s s' t (s.mem.readW a 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldr t n off :: is)) s Q := by
  subst ha
  exact WP.cons (exec_ldr ho hin) (k _ (Upd.setReg _ _ _))

theorem wp_str {t n : Reg} {off : Nat} {a : Addr} (ho : off < 4096)
    (ha : State.addr (s.gpr n + BitVec.ofNat 32 off) = a) (hout : InRegions s.wr a 4)
    (k : ∀ s', VG.Proof.X25519.Arm.Mupd s s' (s.mem.writeW a (s.gpr t)) → WP isa (.block is) s' Q) :
    WP isa (.block (.str t n off :: is)) s Q := by
  subst ha
  exact WP.cons (exec_str ho hout) (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩)

theorem wp_ldrb {t n : Reg} {off : Nat} {a : Addr} (ho : off < 4096)
    (ha : State.addr (s.gpr n + BitVec.ofNat 32 off) = a) (hin : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ s', VG.Proof.X25519.Arm.Upd s s' t ((s.mem a).setWidth 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldrb t n off :: is)) s Q := by
  subst ha
  exact WP.cons (s' := s.setReg t ((s.mem _).setWidth 32))
    (by simp only [exec, ho, ↓reduceIte, State.load8, hin, Option.map_some]) (k _ (Upd.setReg _ _ _))

theorem wp_strb {t n : Reg} {off : Nat} {a : Addr} (ho : off < 4096)
    (ha : State.addr (s.gpr n + BitVec.ofNat 32 off) = a) (hout : InRegions s.wr a 1)
    (k : ∀ s', VG.Proof.X25519.Arm.Mupd s s' (s.mem.writeW a ((s.gpr t).setWidth 8)) → WP isa (.block is) s' Q) :
    WP isa (.block (.strb t n off :: is)) s Q := by
  subst ha
  exact WP.cons (s' := { s with mem := s.mem.writeW _ ((s.gpr t).setWidth 8) })
    (by simp only [exec, ho, ↓reduceIte, State.store8, hout]) (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩)

end

/-- Running `l ++ rest` by running `l` first. -/
theorem WP.append {l rest : List Instr} {s : State} {P Q : State → Prop}
    (h : WP isa (.block l) s P) (k : ∀ s', P s' → WP isa (.block rest) s' Q) :
    WP isa (.block (l ++ rest)) s Q :=
  WP.block_append_iff.mpr (WP.mono h k)

theorem eval_ne (s : State) : isa.eval .ne s = some !s.z := rfl
theorem eval_eq (s : State) : isa.eval .eq s = some s.z := rfl

/-! ## 32-bit arithmetic -/

theorem toNat_add_lt {x y : BitVec 32} (h : x.toNat + y.toNat < 2 ^ 32) :
    (x + y).toNat = x.toNat + y.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]

theorem toNat_sub_le {x y : BitVec 32} (h : y.toNat ≤ x.toNat) : (x - y).toNat = x.toNat - y.toNat := by
  rw [BitVec.toNat_sub_of_le (by simpa [BitVec.le_def] using h)]

theorem toNat_mul_lt {x y : BitVec 32} (h : x.toNat * y.toNat < 2 ^ 32) :
    (x * y).toNat = x.toNat * y.toNat := by
  rw [BitVec.toNat_mul, Nat.mod_eq_of_lt h]

theorem toNat_shr (x : BitVec 32) (n : Nat) : (x >>> n).toNat = x.toNat / 2 ^ n := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem toNat_shl (x : BitVec 32) (n : Nat) : (x <<< n).toNat = x.toNat * 2 ^ n % 2 ^ 32 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

/-- The mask of a limb, as `movw` builds it. -/
abbrev mask16 : BitVec 32 := (0xffff : BitVec 16).setWidth 32

theorem toNat_and_mask16 (x : BitVec 32) : (x &&& VG.Proof.X25519.Arm.mask16).toNat = x.toNat % 65536 := by
  rw [BitVec.toNat_and, show mask16.toNat = 2 ^ 16 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem toNat_imm {v : Nat} (h : v < 2 ^ 32) : (BitVec.ofNat 32 v).toNat = v := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem ofNat_beq_zero {k : Nat} (h : k < 2 ^ 32) : (BitVec.ofNat 32 k == 0) = decide (k = 0) := by
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this
    exact hk this

/-! ## Words at offsets from a base -/

/-- The word at `P + d`, as a number. -/
def wd (m : Mem) (P : Addr) (d : Nat) : Nat := (m.readW (P + BitVec.ofNat 64 d) 32).toNat

theorem wd_lt (m : Mem) (P : Addr) (d : Nat) : VG.Proof.X25519.Arm.wd m P d < 2 ^ 32 := (m.readW _ 32).isLt

theorem wd_write_self (m : Mem) (P : Addr) (d : Nat) (v : BitVec 32) :
    VG.Proof.X25519.Arm.wd (m.writeW (P + BitVec.ofNat 64 d) v) P d = v.toNat := by
  rw [VG.Proof.X25519.Arm.wd, Mem.readW_writeW_self32]

theorem wd_write_other (m : Mem) (P : Addr) {d e : Nat} (v : BitVec 32) (h : d + 4 ≤ e ∨ e + 4 ≤ d)
    (hd : d + 4 ≤ 2 ^ 64) (he : e + 4 ≤ 2 ^ 64) :
    VG.Proof.X25519.Arm.wd (m.writeW (P + BitVec.ofNat 64 e) v) P d = VG.Proof.X25519.Arm.wd m P d := by
  rw [VG.Proof.X25519.Arm.wd, Mem.readW_writeW_sep (Offset.sep P h hd he) (by decide), VG.Proof.X25519.Arm.wd]

theorem wd_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {P : Addr} {d : Nat}
    (hd : ∀ r ∈ rs, (⟨P + BitVec.ofNat 64 d, 4⟩ : Region).Disjoint r) : VG.Proof.X25519.Arm.wd m' P d = VG.Proof.X25519.Arm.wd m P d := by
  rw [VG.Proof.X25519.Arm.wd, VG.Proof.X25519.Arm.wd, hf.readW (Region.contains_self _ _) hd (by decide)]

/-- An address `pb + off` of a base register, as a 64-bit address, if it does not wrap. -/
theorem ea {pb : BitVec 32} {off : Nat} (h : pb.toNat + off < 2 ^ 32) :
    State.addr (pb + BitVec.ofNat 32 off) = State.addr pb + BitVec.ofNat 64 off := addr_add h

theorem addr_toNat (a : BitVec 32) : (State.addr a).toNat = a.toNat := by
  simp only [State.addr, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (Nat.lt_trans a.isLt (by decide))

/-- An access at an offset of a region at an offset of `P`. -/
theorem in_off {rs : List Region} {P : Addr} {a len d n : Nat} (hr : (⟨P + BitVec.ofNat 64 a, len⟩ : Region) ∈ rs)
    (h1 : a ≤ d) (h2 : d + n ≤ a + len) (h3 : a + len < 2 ^ 64) :
    InRegions rs (P + BitVec.ofNat 64 d) n := ⟨_, hr, Offset.contains P h1 h2 h3⟩

theorem in_base {rs : List Region} {P : Addr} {len d n : Nat} (hr : (⟨P, len⟩ : Region) ∈ rs)
    (h : d + n ≤ len) (h3 : d < 2 ^ 64) : InRegions rs (P + BitVec.ofNat 64 d) n :=
  ⟨_, hr, Offset.contains_base P h h3⟩

end VG.Proof.X25519.Arm

end
