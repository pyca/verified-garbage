import VerifiedGarbage.Proof.X25519.Bytes
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Impl.X25519.AArch64
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import Mathlib.Logic.Function.Basic
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Spec.X25519.Contract
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.AArch64.Arith`. -/
section

/-!
# X25519 on AArch64: field elements as fifteen 17-bit limbs

The numbers the code of `Impl/X25519/AArch64.lean` computes, as natural
numbers: the limbs `f 0, …, f 14` stand for `val15 f = Σ f i · 2^(17 i)`, and
each operation is a function of the limbs, computed as the machine does
(modulo `2⁶⁴`); here they are shown to compute the field operations, for limbs
within bounds (`Bnd f k`: every limb is less than `2^k`).
-/

namespace VG.Proof.X25519.AArch64

open VG.Spec.X25519 VG.Proof.X25519

/-- `Σ_{i < n} f i · 2^(17 i)`. -/
def valN (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => VG.Proof.X25519.AArch64.valN f n + f n * 2 ^ (17 * n)

/-- The number with the limbs `f 0, …, f 14`. -/
abbrev val15 (f : Nat → Nat) : Nat := VG.Proof.X25519.AArch64.valN f 15

/-- Every limb is less than `2^k`. -/
def Bnd (f : Nat → Nat) (k : Nat) : Prop := ∀ i < 15, f i < 2 ^ k

theorem Bnd.mono {f : Nat → Nat} {k k' : Nat} (h : VG.Proof.X25519.AArch64.Bnd f k) (hk : k ≤ k') : VG.Proof.X25519.AArch64.Bnd f k' :=
  fun i hi => Nat.lt_of_lt_of_le (h i hi) (Nat.pow_le_pow_right (by decide) hk)

theorem valN_congr {f g : Nat → Nat} {n : Nat} (h : ∀ i < n, f i = g i) : VG.Proof.X25519.AArch64.valN f n = VG.Proof.X25519.AArch64.valN g n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [VG.Proof.X25519.AArch64.valN, VG.Proof.X25519.AArch64.valN, ih fun i hi => h i (by omega), h n (by omega)]

theorem valN_lt {f : Nat → Nat} {n : Nat} (h : ∀ i < n, f i < 2 ^ 17) : VG.Proof.X25519.AArch64.valN f n < 2 ^ (17 * n) := by
  induction n with
  | zero => simp [VG.Proof.X25519.AArch64.valN]
  | succ n ih =>
    rw [VG.Proof.X25519.AArch64.valN]
    have h1 := ih fun i hi => h i (by omega)
    have h2 := h n (by omega)
    have : f n * 2 ^ (17 * n) + 2 ^ (17 * n) ≤ 2 ^ 17 * 2 ^ (17 * n) := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ h2
    rw [show 17 * (n + 1) = 17 + 17 * n by omega, Nat.pow_add]
    omega

/-! ## Products -/

theorem valN_mul (c : Nat) (f : Nat → Nat) (n : Nat) : VG.Proof.X25519.AArch64.valN (fun i => f i * c) n = c * VG.Proof.X25519.AArch64.valN f n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [VG.Proof.X25519.AArch64.valN, ih, Nat.mul_add]; rw [Nat.mul_comm (f n) c, Nat.mul_assoc]

theorem valN_add (f g : Nat → Nat) (n : Nat) : VG.Proof.X25519.AArch64.valN (fun i => f i + g i) n = VG.Proof.X25519.AArch64.valN f n + VG.Proof.X25519.AArch64.valN g n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [VG.Proof.X25519.AArch64.valN, ih, Nat.add_mul]; omega

theorem valN_add_split (h : Nat → Nat) (a : Nat) :
    ∀ b, VG.Proof.X25519.AArch64.valN h (a + b) = VG.Proof.X25519.AArch64.valN h a + 2 ^ (17 * a) * VG.Proof.X25519.AArch64.valN (fun j => h (a + j)) b
  | 0 => by rw [Nat.add_zero, VG.Proof.X25519.AArch64.valN, Nat.mul_zero, Nat.add_zero]
  | b + 1 => by
    rw [← Nat.add_assoc, VG.Proof.X25519.AArch64.valN, VG.Proof.X25519.AArch64.valN_add_split h a b, VG.Proof.X25519.AArch64.valN, show 17 * (a + b) = 17 * a + 17 * b by omega,
      Nat.pow_add]
    generalize 2 ^ (17 * a) = A
    generalize 2 ^ (17 * b) = C
    grind

theorem valN_zero {h : Nat → Nat} : ∀ {n}, (∀ k < n, h k = 0) → VG.Proof.X25519.AArch64.valN h n = 0
  | 0, _ => rfl
  | n + 1, hz => by rw [VG.Proof.X25519.AArch64.valN, VG.Proof.X25519.AArch64.valN_zero fun k hk => hz k (by omega), hz n (by omega), Nat.zero_mul]

/-- `Σ_{i < n} t i`. -/
def sumR (t : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => VG.Proof.X25519.AArch64.sumR t n + t n

theorem sumR_congr {t u : Nat → Nat} {n : Nat} (h : ∀ i < n, t i = u i) : VG.Proof.X25519.AArch64.sumR t n = VG.Proof.X25519.AArch64.sumR u n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [VG.Proof.X25519.AArch64.sumR, VG.Proof.X25519.AArch64.sumR, ih fun i hi => h i (by omega), h n (by omega)]

theorem sumR_zero {t : Nat → Nat} : ∀ {n}, (∀ i < n, t i = 0) → VG.Proof.X25519.AArch64.sumR t n = 0
  | 0, _ => rfl
  | n + 1, hz => by rw [VG.Proof.X25519.AArch64.sumR, VG.Proof.X25519.AArch64.sumR_zero fun i hi => hz i (by omega), hz n (by omega)]

theorem sumR_split (t : Nat → Nat) (a : Nat) :
    ∀ b, VG.Proof.X25519.AArch64.sumR t (a + b) = VG.Proof.X25519.AArch64.sumR t a + VG.Proof.X25519.AArch64.sumR (fun j => t (a + j)) b
  | 0 => rfl
  | b + 1 => by rw [← Nat.add_assoc, VG.Proof.X25519.AArch64.sumR, VG.Proof.X25519.AArch64.sumR_split t a b, VG.Proof.X25519.AArch64.sumR, Nat.add_assoc]

/-- The products of column `k` that do not fold. -/
def lo (f g : Nat → Nat) (k : Nat) : Nat := VG.Proof.X25519.AArch64.sumR (fun i => f i * g (k - i)) (k + 1)

/-- The products `f (k + 1 + j) · g (14 - j)` that fold into column `k`. -/
def hi (f g : Nat → Nat) (k : Nat) : Nat := VG.Proof.X25519.AArch64.sumR (fun j => f (k + 1 + j) * g (14 - j)) (14 - k)

/-- Row `n`'s product in column `k`: `f n · g (k - n)`, if `g` has a limb there. -/
def term (f g : Nat → Nat) (n k : Nat) : Nat := if n ≤ k ∧ k - n < 15 then f n * g (k - n) else 0

theorem term_eq {f g : Nat → Nat} {n k : Nat} (h : n ≤ k ∧ k - n < 15) :
    VG.Proof.X25519.AArch64.term f g n k = f n * g (k - n) := by
  simp only [VG.Proof.X25519.AArch64.term, h, and_self, ite_true]

theorem term_eq_zero {f g : Nat → Nat} {n k : Nat} (h : ¬ (n ≤ k ∧ k - n < 15)) : VG.Proof.X25519.AArch64.term f g n k = 0 := by
  simp only [VG.Proof.X25519.AArch64.term, h, ite_false]

/-- Column `k` of the first `n` rows. -/
def colsum (f g : Nat → Nat) (n k : Nat) : Nat := VG.Proof.X25519.AArch64.sumR (fun i => VG.Proof.X25519.AArch64.term f g i k) n

/-- Row `n` is `f n · 2^(17 n) · g`. -/
theorem row_val (f g : Nat → Nat) {n : Nat} (hn : n ≤ 14) :
    VG.Proof.X25519.AArch64.valN (VG.Proof.X25519.AArch64.term f g n) 29 = 2 ^ (17 * n) * (f n * VG.Proof.X25519.AArch64.valN g 15) := by
  have z1 : VG.Proof.X25519.AArch64.valN (VG.Proof.X25519.AArch64.term f g n) n = 0 := VG.Proof.X25519.AArch64.valN_zero fun k hk => VG.Proof.X25519.AArch64.term_eq_zero (by omega)
  have z2 : VG.Proof.X25519.AArch64.valN (fun j => VG.Proof.X25519.AArch64.term f g n (n + (15 + j))) (14 - n) = 0 :=
    VG.Proof.X25519.AArch64.valN_zero fun k _ => VG.Proof.X25519.AArch64.term_eq_zero (by omega)
  have e3 : VG.Proof.X25519.AArch64.valN (fun j => VG.Proof.X25519.AArch64.term f g n (n + j)) 15 = f n * VG.Proof.X25519.AArch64.valN g 15 := by
    rw [VG.Proof.X25519.AArch64.valN_congr (g := fun j => g j * f n) fun j hj => by
      rw [VG.Proof.X25519.AArch64.term_eq (by omega), Nat.add_sub_cancel_left, Nat.mul_comm], VG.Proof.X25519.AArch64.valN_mul]
  rw [show 29 = n + (15 + (14 - n)) by omega, VG.Proof.X25519.AArch64.valN_add_split, VG.Proof.X25519.AArch64.valN_add_split (fun j => VG.Proof.X25519.AArch64.term f g n (n + j)),
    z1, z2, e3, Nat.mul_zero, Nat.add_zero, Nat.zero_add]

/-- Product scanning: `f · g` is the sum of its 29 columns. -/
theorem prod_cols (f g : Nat → Nat) : ∀ n ≤ 15, VG.Proof.X25519.AArch64.valN f n * VG.Proof.X25519.AArch64.valN g 15 = VG.Proof.X25519.AArch64.valN (VG.Proof.X25519.AArch64.colsum f g n) 29
  | 0, _ => by rw [VG.Proof.X25519.AArch64.valN, Nat.zero_mul]; exact (VG.Proof.X25519.AArch64.valN_zero fun _ _ => rfl).symm
  | n + 1, hn => by
    rw [VG.Proof.X25519.AArch64.valN, Nat.add_mul, VG.Proof.X25519.AArch64.prod_cols f g n (by omega), Nat.mul_comm (f n), Nat.mul_assoc,
      ← VG.Proof.X25519.AArch64.row_val f g (by omega), ← VG.Proof.X25519.AArch64.valN_add]
    rfl

theorem colsum_lo (f g : Nat → Nat) {k : Nat} (hk : k < 15) : VG.Proof.X25519.AArch64.colsum f g 15 k = VG.Proof.X25519.AArch64.lo f g k := by
  have e := VG.Proof.X25519.AArch64.sumR_split (fun i => VG.Proof.X25519.AArch64.term f g i k) (k + 1) (14 - k)
  rw [show k + 1 + (14 - k) = 15 by omega,
    VG.Proof.X25519.AArch64.sumR_zero (n := 14 - k) (t := fun j => VG.Proof.X25519.AArch64.term f g (k + 1 + j) k) fun j _ => VG.Proof.X25519.AArch64.term_eq_zero (by omega),
    Nat.add_zero] at e
  rw [VG.Proof.X25519.AArch64.colsum, e, VG.Proof.X25519.AArch64.lo]
  exact VG.Proof.X25519.AArch64.sumR_congr fun i hi => VG.Proof.X25519.AArch64.term_eq (by omega)

theorem colsum_hi (f g : Nat → Nat) {k : Nat} (hk : k < 14) :
    VG.Proof.X25519.AArch64.colsum f g 15 (15 + k) = VG.Proof.X25519.AArch64.hi f g k := by
  have e := VG.Proof.X25519.AArch64.sumR_split (fun i => VG.Proof.X25519.AArch64.term f g i (15 + k)) (k + 1) (14 - k)
  rw [show k + 1 + (14 - k) = 15 by omega,
    VG.Proof.X25519.AArch64.sumR_zero (n := k + 1) (t := fun i => VG.Proof.X25519.AArch64.term f g i (15 + k)) fun i hi => VG.Proof.X25519.AArch64.term_eq_zero (by omega),
    Nat.zero_add] at e
  rw [VG.Proof.X25519.AArch64.colsum, e, VG.Proof.X25519.AArch64.hi]
  refine VG.Proof.X25519.AArch64.sumR_congr fun j hj => ?_
  rw [VG.Proof.X25519.AArch64.term_eq (by omega), show 15 + k - (k + 1 + j) = 14 - j by omega]

/-- The columns that do not fold, and `2²⁵⁵` times those that do. -/
theorem product_eq (f g : Nat → Nat) :
    VG.Proof.X25519.AArch64.valN f 15 * VG.Proof.X25519.AArch64.valN g 15 = VG.Proof.X25519.AArch64.valN (VG.Proof.X25519.AArch64.lo f g) 15 + 2 ^ 255 * VG.Proof.X25519.AArch64.valN (VG.Proof.X25519.AArch64.hi f g) 15 := by
  have h15 : VG.Proof.X25519.AArch64.valN (VG.Proof.X25519.AArch64.hi f g) 15 = VG.Proof.X25519.AArch64.valN (VG.Proof.X25519.AArch64.hi f g) 14 := by
    show VG.Proof.X25519.AArch64.valN (VG.Proof.X25519.AArch64.hi f g) 14 + VG.Proof.X25519.AArch64.hi f g 14 * 2 ^ (17 * 14) = _
    rw [show VG.Proof.X25519.AArch64.hi f g 14 = 0 from rfl, Nat.zero_mul, Nat.add_zero]
  rw [VG.Proof.X25519.AArch64.prod_cols f g 15 (Nat.le_refl _), show 29 = 15 + 14 from rfl, VG.Proof.X25519.AArch64.valN_add_split,
    VG.Proof.X25519.AArch64.valN_congr fun k hk => VG.Proof.X25519.AArch64.colsum_lo f g hk, VG.Proof.X25519.AArch64.valN_congr fun k hk => VG.Proof.X25519.AArch64.colsum_hi f g hk, h15]

theorem valN_lin (a b : Nat → Nat) (c n : Nat) :
    VG.Proof.X25519.AArch64.valN (fun k => a k + c * b k) n = VG.Proof.X25519.AArch64.valN a n + c * VG.Proof.X25519.AArch64.valN b n := by
  rw [VG.Proof.X25519.AArch64.valN_add, VG.Proof.X25519.AArch64.valN_congr (g := fun k => b k * c) fun k _ => Nat.mul_comm _ _, VG.Proof.X25519.AArch64.valN_mul]

/-- The columns of the product of `f` and `g`, folded: a number congruent to
the product. -/
theorem product (f g : Nat → Nat) :
    toFe (VG.Proof.X25519.AArch64.valN (fun k => VG.Proof.X25519.AArch64.lo f g k + 19 * VG.Proof.X25519.AArch64.hi f g k) 15) = toFe (VG.Proof.X25519.AArch64.valN f 15) * toFe (VG.Proof.X25519.AArch64.valN g 15) :=
  toFe_mul (by rw [VG.Proof.X25519.AArch64.valN_lin, VG.Proof.X25519.AArch64.product_eq, fold255])

/-! ## The product, as the code computes it -/

/-- Column `k` as the code computes it (modulo `2⁶⁴`). -/
def colM (f g : Nat → Nat) (k : Nat) : Nat := (VG.Proof.X25519.AArch64.lo f g k % 2 ^ 64 + VG.Proof.X25519.AArch64.hi f g k % 2 ^ 64 * 19) % 2 ^ 64

/-- The columns (zero beyond the fifteenth). -/
def cols (f g : Nat → Nat) (k : Nat) : Nat := if k < 15 then VG.Proof.X25519.AArch64.colM f g k else 0

theorem prod_le {f g : Nat → Nat} (hf : VG.Proof.X25519.AArch64.Bnd f 26) (hg : VG.Proof.X25519.AArch64.Bnd g 26) {i j : Nat} (hi : i < 15)
    (hj : j < 15) : f i * g j ≤ 2 ^ 52 :=
  Nat.le_trans (Nat.mul_le_mul (Nat.le_of_lt (hf i hi)) (Nat.le_of_lt (hg j hj))) (by decide)

theorem sum_le {t : Nat → Nat} {c : Nat} : ∀ n, (∀ i < n, t i ≤ c) → VG.Proof.X25519.AArch64.sumR t n ≤ n * c
  | 0, _ => Nat.zero_le _
  | n + 1, h => by
    rw [VG.Proof.X25519.AArch64.sumR, Nat.succ_mul]
    exact Nat.add_le_add (VG.Proof.X25519.AArch64.sum_le n fun i hi => h i (by omega)) (h n (by omega))

theorem lo_le {f g : Nat → Nat} (hf : VG.Proof.X25519.AArch64.Bnd f 26) (hg : VG.Proof.X25519.AArch64.Bnd g 26) {k : Nat} (hk : k < 15) :
    VG.Proof.X25519.AArch64.lo f g k ≤ 15 * 2 ^ 52 :=
  Nat.le_trans (VG.Proof.X25519.AArch64.sum_le (k + 1) fun i hi => VG.Proof.X25519.AArch64.prod_le hf hg (by omega) (by omega))
    (Nat.mul_le_mul_right _ (by omega))

theorem hi_le {f g : Nat → Nat} (hf : VG.Proof.X25519.AArch64.Bnd f 26) (hg : VG.Proof.X25519.AArch64.Bnd g 26) {k : Nat} (hk : k < 15) :
    VG.Proof.X25519.AArch64.hi f g k ≤ 15 * 2 ^ 52 :=
  Nat.le_trans (VG.Proof.X25519.AArch64.sum_le (14 - k) fun j hj => VG.Proof.X25519.AArch64.prod_le hf hg (by omega) (by omega))
    (Nat.mul_le_mul_right _ (by omega))

theorem colM_eq {f g : Nat → Nat} (hf : VG.Proof.X25519.AArch64.Bnd f 26) (hg : VG.Proof.X25519.AArch64.Bnd g 26) {k : Nat} (hk : k < 15) :
    VG.Proof.X25519.AArch64.colM f g k = VG.Proof.X25519.AArch64.lo f g k + 19 * VG.Proof.X25519.AArch64.hi f g k ∧ VG.Proof.X25519.AArch64.colM f g k ≤ 2 ^ 61 := by
  have h1 := VG.Proof.X25519.AArch64.lo_le hf hg hk
  have h2 := VG.Proof.X25519.AArch64.hi_le hf hg hk
  simp only [VG.Proof.X25519.AArch64.colM]
  rw [Nat.mod_eq_of_lt (by omega : lo f g k < 2 ^ 64), Nat.mod_eq_of_lt (by omega : hi f g k < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega)]
  omega

theorem cols_spec {f g : Nat → Nat} (hf : VG.Proof.X25519.AArch64.Bnd f 26) (hg : VG.Proof.X25519.AArch64.Bnd g 26) :
    (∀ k < 15, VG.Proof.X25519.AArch64.cols f g k ≤ 2 ^ 61) ∧ toFe (VG.Proof.X25519.AArch64.val15 (VG.Proof.X25519.AArch64.cols f g)) = toFe (VG.Proof.X25519.AArch64.val15 f) * toFe (VG.Proof.X25519.AArch64.val15 g) := by
  refine ⟨fun k hk => ?_, ?_⟩
  · simp only [VG.Proof.X25519.AArch64.cols, hk, ite_true]; exact (VG.Proof.X25519.AArch64.colM_eq hf hg hk).2
  · rw [← VG.Proof.X25519.AArch64.product]
    refine congrArg toFe ?_
    exact VG.Proof.X25519.AArch64.valN_congr fun k hk => by simp only [VG.Proof.X25519.AArch64.cols, hk, ite_true]; exact (VG.Proof.X25519.AArch64.colM_eq hf hg hk).1

/-! ## Carries -/

/-- The carry out of limb `k` into limb `k'`, as the code computes it. -/
def cstep (k k' : Nat) (f : Nat → Nat) (i : Nat) : Nat :=
  if i = k then f k % 2 ^ 17 else if i = k' then (f k' + f k / 2 ^ 17) % 2 ^ 64 else f i

/-- The carries from limb 0 to limb `n`. -/
def chainN (f : Nat → Nat) : Nat → Nat → Nat
  | 0 => f
  | n + 1 => VG.Proof.X25519.AArch64.cstep n (n + 1) (VG.Proof.X25519.AArch64.chainN f n)

/-- The carry out of limb 14 folded into limb 0, as 19 times it. -/
def cfold (f : Nat → Nat) (i : Nat) : Nat :=
  if i = 14 then f 14 % 2 ^ 17 else if i = 0 then (f 0 + f 14 / 2 ^ 17 * 19) % 2 ^ 64 else f i

/-- The carries of `carry`. -/
def carryF (f : Nat → Nat) : Nat → Nat := VG.Proof.X25519.AArch64.cstep 1 2 (VG.Proof.X25519.AArch64.cstep 0 1 (VG.Proof.X25519.AArch64.cfold (VG.Proof.X25519.AArch64.chainN f 14)))

/-- Two limbs that stand for the same number. -/
theorem valN_two {f g : Nat → Nat} {k n : Nat} (hn : k + 2 ≤ n) (hlo : ∀ i < k, g i = f i)
    (hhi : ∀ i, k + 1 < i → g i = f i) (h : g k + 2 ^ 17 * g (k + 1) = f k + 2 ^ 17 * f (k + 1)) :
    VG.Proof.X25519.AArch64.valN g n = VG.Proof.X25519.AArch64.valN f n := by
  induction hn with
  | refl =>
    simp only [VG.Proof.X25519.AArch64.valN]
    rw [VG.Proof.X25519.AArch64.valN_congr hlo, show 17 * (k + 1) = 17 * k + 17 by omega, Nat.pow_add]
    have e : g k * 2 ^ (17 * k) + g (k + 1) * (2 ^ (17 * k) * 2 ^ 17) =
        (g k + 2 ^ 17 * g (k + 1)) * 2 ^ (17 * k) := by
      rw [Nat.add_mul, Nat.mul_comm (2 ^ 17), Nat.mul_assoc, Nat.mul_comm (2 ^ 17)]
    have e' : f k * 2 ^ (17 * k) + f (k + 1) * (2 ^ (17 * k) * 2 ^ 17) =
        (f k + 2 ^ 17 * f (k + 1)) * 2 ^ (17 * k) := by
      rw [Nat.add_mul, Nat.mul_comm (2 ^ 17), Nat.mul_assoc, Nat.mul_comm (2 ^ 17)]
    rw [Nat.add_assoc, e, h, ← e', ← Nat.add_assoc]
  | @step n hn ih => rw [VG.Proof.X25519.AArch64.valN, VG.Proof.X25519.AArch64.valN, ih, hhi n (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hn)]

theorem cstep_val {f : Nat → Nat} {k : Nat} (hk : k + 2 ≤ 15)
    (h : f (k + 1) + f k / 2 ^ 17 < 2 ^ 64) : VG.Proof.X25519.AArch64.valN (VG.Proof.X25519.AArch64.cstep k (k + 1) f) 15 = VG.Proof.X25519.AArch64.valN f 15 := by
  refine VG.Proof.X25519.AArch64.valN_two hk (fun i hi => ?_) (fun i hi => ?_) ?_
  · simp only [VG.Proof.X25519.AArch64.cstep, show i ≠ k by omega, show i ≠ k + 1 by omega, ite_false]
  · simp only [VG.Proof.X25519.AArch64.cstep, show i ≠ k by omega, show i ≠ k + 1 by omega, ite_false]
  · simp only [VG.Proof.X25519.AArch64.cstep, ite_true, show k + 1 ≠ k by omega, ite_false]
    rw [Nat.mod_eq_of_lt h]
    omega

theorem chainN_spec {f : Nat → Nat} {M : Nat} (hM : M + M / 2 ^ 16 < 2 ^ 64)
    (hf : ∀ i < 15, f i ≤ M) {n : Nat} (hn : n ≤ 14) :
    (∀ i < n, VG.Proof.X25519.AArch64.chainN f n i < 2 ^ 17) ∧ VG.Proof.X25519.AArch64.chainN f n n ≤ M + M / 2 ^ 16 ∧
      (∀ i, n < i → VG.Proof.X25519.AArch64.chainN f n i = f i) ∧ VG.Proof.X25519.AArch64.valN (VG.Proof.X25519.AArch64.chainN f n) 15 = VG.Proof.X25519.AArch64.valN f 15 := by
  induction n with
  | zero =>
    refine ⟨fun i hi => absurd hi (Nat.not_lt_zero _), ?_, fun _ _ => rfl, rfl⟩
    have := hf 0 (by decide)
    exact Nat.le_trans this (Nat.le_add_right _ _)
  | succ n ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih (by omega)
    have hn1 : VG.Proof.X25519.AArch64.chainN f n (n + 1) = f (n + 1) := h3 (n + 1) (by omega)
    have hf1 := hf (n + 1) (by omega)
    have hc : VG.Proof.X25519.AArch64.chainN f n n / 2 ^ 17 ≤ M / 2 ^ 16 := by omega
    have hsum : VG.Proof.X25519.AArch64.chainN f n (n + 1) + VG.Proof.X25519.AArch64.chainN f n n / 2 ^ 17 < 2 ^ 64 := by omega
    simp only [VG.Proof.X25519.AArch64.chainN]
    refine ⟨fun i hi => ?_, ?_, fun i hi => ?_, ?_⟩
    · simp only [VG.Proof.X25519.AArch64.cstep]
      by_cases hin : i = n
      · rw [ite_eq_left hin]; exact Nat.mod_lt _ (by decide)
      · rw [ite_eq_right hin, ite_eq_right (by omega)]; exact h1 i (by omega)
    · simp only [VG.Proof.X25519.AArch64.cstep, show n + 1 ≠ n by omega, ite_false, ite_true]
      rw [Nat.mod_eq_of_lt hsum]; omega
    · simp only [VG.Proof.X25519.AArch64.cstep, show i ≠ n by omega, show i ≠ n + 1 by omega, ite_false]
      exact h3 i (by omega)
    · rw [VG.Proof.X25519.AArch64.cstep_val (by omega) hsum, h4]

theorem chainN_beyond {f : Nat → Nat} {n i : Nat} (hn : n ≤ 14) (hi : 15 ≤ i) : VG.Proof.X25519.AArch64.chainN f n i = f i := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [VG.Proof.X25519.AArch64.chainN, VG.Proof.X25519.AArch64.cstep, show i ≠ n by omega, show i ≠ n + 1 by omega, ite_false]
    exact ih (by omega)

/-- Folding the carry out of limb 14, as numbers. -/
theorem cfold_valN {f : Nat → Nat} (h : f 0 + f 14 / 2 ^ 17 * 19 < 2 ^ 64) :
    VG.Proof.X25519.AArch64.val15 (VG.Proof.X25519.AArch64.cfold f) + 2 ^ 255 * (f 14 / 2 ^ 17) = VG.Proof.X25519.AArch64.val15 f + 19 * (f 14 / 2 ^ 17) := by
  have hc : ∀ i, 0 < i → i < 14 → VG.Proof.X25519.AArch64.cfold f i = f i := fun i h0 h14 => by
    simp only [VG.Proof.X25519.AArch64.cfold, show i ≠ 14 by omega, show i ≠ 0 by omega, ite_false]
  have h0 : VG.Proof.X25519.AArch64.cfold f 0 = f 0 + f 14 / 2 ^ 17 * 19 := by
    simp only [VG.Proof.X25519.AArch64.cfold, show (0 : Nat) ≠ 14 by decide, ite_false, ite_true]; exact Nat.mod_eq_of_lt h
  have h14 : VG.Proof.X25519.AArch64.cfold f 14 = f 14 % 2 ^ 17 := by simp only [VG.Proof.X25519.AArch64.cfold, ite_true]
  simp only [VG.Proof.X25519.AArch64.val15, VG.Proof.X25519.AArch64.valN, h0, h14, hc 1 (by decide) (by decide), hc 2 (by decide) (by decide),
    hc 3 (by decide) (by decide), hc 4 (by decide) (by decide), hc 5 (by decide) (by decide),
    hc 6 (by decide) (by decide), hc 7 (by decide) (by decide), hc 8 (by decide) (by decide),
    hc 9 (by decide) (by decide), hc 10 (by decide) (by decide), hc 11 (by decide) (by decide),
    hc 12 (by decide) (by decide), hc 13 (by decide) (by decide)]
  omega

/-- Folding the carry out of limb 14 does not change the number modulo `p`. -/
theorem cfold_val {f : Nat → Nat} (h : f 0 + f 14 / 2 ^ 17 * 19 < 2 ^ 64) :
    toFe (VG.Proof.X25519.AArch64.val15 (VG.Proof.X25519.AArch64.cfold f)) = toFe (VG.Proof.X25519.AArch64.val15 f) := by
  have e' := congrArg toFe (VG.Proof.X25519.AArch64.cfold_valN h)
  rw [toFe_add rfl, toFe_add rfl,
    toFe_congr (by have := fold255 0 (f 14 / 2 ^ 17); rwa [Nat.zero_add, Nat.zero_add] at this :
      2 ^ 255 * (f 14 / 2 ^ 17) % P = 19 * (f 14 / 2 ^ 17) % P)] at e'
  grind

theorem cfold_beyond {f : Nat → Nat} {i : Nat} (hi : 15 ≤ i) : VG.Proof.X25519.AArch64.cfold f i = f i := by
  simp only [VG.Proof.X25519.AArch64.cfold, show i ≠ 14 by omega, show i ≠ 0 by omega, ite_false]

theorem cstep_beyond {f : Nat → Nat} {k k' i : Nat} (hk : k < 15) (hk' : k' < 15) (hi : 15 ≤ i) :
    VG.Proof.X25519.AArch64.cstep k k' f i = f i := by
  simp only [VG.Proof.X25519.AArch64.cstep, show i ≠ k by omega, show i ≠ k' by omega, ite_false]

/-- The carries of a product: from limbs of at most `2⁶¹`, limbs below `2¹⁸`
standing for the same number modulo `p`. -/
theorem carryF_spec {f : Nat → Nat} (hf : ∀ i < 15, f i ≤ 2 ^ 61) :
    VG.Proof.X25519.AArch64.Bnd (VG.Proof.X25519.AArch64.carryF f) 18 ∧ toFe (VG.Proof.X25519.AArch64.val15 (VG.Proof.X25519.AArch64.carryF f)) = toFe (VG.Proof.X25519.AArch64.val15 f) ∧ ∀ i, 15 ≤ i → VG.Proof.X25519.AArch64.carryF f i = f i := by
  obtain ⟨c1, c2, c3, c4⟩ := VG.Proof.X25519.AArch64.chainN_spec (M := 2 ^ 61) (by decide) hf (n := 14) (by decide)
  generalize hg : VG.Proof.X25519.AArch64.chainN f 14 = g at c1 c2 c3 c4
  have g0 := c1 0 (by decide)
  have g1 := c1 1 (by decide)
  have g2 := c1 2 (by decide)
  have hfold : g 0 + g 14 / 2 ^ 17 * 19 < 2 ^ 64 := by omega
  have v1 := VG.Proof.X25519.AArch64.cfold_val hfold
  generalize hg1 : VG.Proof.X25519.AArch64.cfold g = g1 at v1
  have e0 : g1 0 = g 0 + g 14 / 2 ^ 17 * 19 := by
    rw [← hg1]; simp only [VG.Proof.X25519.AArch64.cfold, show (0 : Nat) ≠ 14 by decide, ite_false, ite_true]
    exact Nat.mod_eq_of_lt hfold
  have e14 : g1 14 < 2 ^ 17 := by rw [← hg1]; simp only [VG.Proof.X25519.AArch64.cfold, ite_true]; exact Nat.mod_lt _ (by decide)
  have eo : ∀ i, 0 < i → i < 14 → g1 i = g i := fun i h0 h14 => by
    rw [← hg1]; simp only [VG.Proof.X25519.AArch64.cfold, show i ≠ 14 by omega, show i ≠ 0 by omega, ite_false]
  have s1 : g1 1 + g1 0 / 2 ^ 17 < 2 ^ 64 := by rw [eo 1 (by decide) (by decide), e0]; omega
  have v2 := VG.Proof.X25519.AArch64.cstep_val (f := g1) (k := 0) (by decide) s1
  generalize hg2 : VG.Proof.X25519.AArch64.cstep 0 1 g1 = g2 at v2
  have f0 : g2 0 < 2 ^ 17 := by rw [← hg2]; simp only [VG.Proof.X25519.AArch64.cstep, ite_true]; exact Nat.mod_lt _ (by decide)
  have f1 : g2 1 = g1 1 + g1 0 / 2 ^ 17 := by
    rw [← hg2]; simp only [VG.Proof.X25519.AArch64.cstep, show (1 : Nat) ≠ 0 by decide, ite_false, ite_true]
    exact Nat.mod_eq_of_lt s1
  have fo : ∀ i, 1 < i → g2 i = g1 i := fun i h => by
    rw [← hg2]; simp only [VG.Proof.X25519.AArch64.cstep, show i ≠ 0 by omega, show i ≠ 1 by omega, ite_false]
  have s2 : g2 2 + g2 1 / 2 ^ 17 < 2 ^ 64 := by
    rw [fo 2 (by decide), eo 2 (by decide) (by decide), f1, eo 1 (by decide) (by decide), e0]; omega
  have v3 := VG.Proof.X25519.AArch64.cstep_val (f := g2) (k := 1) (by decide) s2
  have hC : VG.Proof.X25519.AArch64.carryF f = VG.Proof.X25519.AArch64.cstep 1 2 g2 := by rw [VG.Proof.X25519.AArch64.carryF, hg, hg1, hg2]
  refine ⟨fun i hi => ?_, ?_, fun i hi => ?_⟩
  · rw [hC]; simp only [VG.Proof.X25519.AArch64.cstep]
    by_cases h1 : i = 1
    · rw [ite_eq_left h1]; exact Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)
    by_cases h2 : i = 2
    · rw [ite_eq_right h1, ite_eq_left h2, Nat.mod_eq_of_lt s2, fo 2 (by decide),
        eo 2 (by decide) (by decide), f1, eo 1 (by decide) (by decide), e0]
      omega
    rw [ite_eq_right h1, ite_eq_right h2]
    by_cases h0 : i = 0
    · subst h0; exact Nat.lt_trans f0 (by decide)
    rw [fo i (by omega)]
    by_cases h14 : i = 14
    · subst h14; exact Nat.lt_trans e14 (by decide)
    rw [eo i (by omega) (by omega)]
    exact Nat.lt_trans (c1 i (by omega)) (by decide)
  · rw [hC]
    rw [congrArg toFe v3, congrArg toFe v2, v1]
    exact congrArg toFe c4
  · simp only [VG.Proof.X25519.AArch64.carryF]
    rw [VG.Proof.X25519.AArch64.cstep_beyond (by decide) (by decide) hi, VG.Proof.X25519.AArch64.cstep_beyond (by decide) (by decide) hi,
      VG.Proof.X25519.AArch64.cfold_beyond hi, VG.Proof.X25519.AArch64.chainN_beyond (by decide) hi]

/-- The product, as `mul` computes it. -/
def mulF (f g : Nat → Nat) : Nat → Nat := VG.Proof.X25519.AArch64.carryF (VG.Proof.X25519.AArch64.cols f g)

theorem mulF_spec {f g : Nat → Nat} (hf : VG.Proof.X25519.AArch64.Bnd f 26) (hg : VG.Proof.X25519.AArch64.Bnd g 26) :
    VG.Proof.X25519.AArch64.Bnd (VG.Proof.X25519.AArch64.mulF f g) 18 ∧ toFe (VG.Proof.X25519.AArch64.val15 (VG.Proof.X25519.AArch64.mulF f g)) = toFe (VG.Proof.X25519.AArch64.val15 f) * toFe (VG.Proof.X25519.AArch64.val15 g) := by
  obtain ⟨h1, h2⟩ := VG.Proof.X25519.AArch64.cols_spec hf hg
  obtain ⟨c1, c2, -⟩ := VG.Proof.X25519.AArch64.carryF_spec h1
  exact ⟨c1, c2.trans h2⟩

/-- The limbs times `a24 = 121665`, as `mulSmall` computes them. -/
def scaleF (f : Nat → Nat) (k : Nat) : Nat := if k < 15 then f k * 121665 % 2 ^ 64 else 0

def mulSmallF (f : Nat → Nat) : Nat → Nat := VG.Proof.X25519.AArch64.carryF (VG.Proof.X25519.AArch64.scaleF f)

theorem mulSmallF_spec {f : Nat → Nat} (hf : VG.Proof.X25519.AArch64.Bnd f 26) :
    VG.Proof.X25519.AArch64.Bnd (VG.Proof.X25519.AArch64.mulSmallF f) 18 ∧ toFe (VG.Proof.X25519.AArch64.val15 (VG.Proof.X25519.AArch64.mulSmallF f)) = a24 * toFe (VG.Proof.X25519.AArch64.val15 f) := by
  have hs : ∀ k < 15, VG.Proof.X25519.AArch64.scaleF f k = f k * 121665 := fun k hk => by
    simp only [VG.Proof.X25519.AArch64.scaleF, hk, ite_true]
    have := hf k hk
    exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨c1, c2, -⟩ := VG.Proof.X25519.AArch64.carryF_spec (f := VG.Proof.X25519.AArch64.scaleF f) fun k hk => by rw [hs k hk]; have := hf k hk; omega
  refine ⟨c1, ?_⟩
  rw [VG.Proof.X25519.AArch64.mulSmallF, c2, VG.Proof.X25519.AArch64.val15, VG.Proof.X25519.AArch64.valN_congr hs, VG.Proof.X25519.AArch64.valN_mul]
  exact toFe_a24 rfl

/-! ## Sums and differences -/

/-- The sum, as `add` computes it. -/
def addF (f g : Nat → Nat) (k : Nat) : Nat := if k < 15 then (f k + g k) % 2 ^ 64 else 0

theorem addF_spec {f g : Nat → Nat} {a b : Nat} (hf : VG.Proof.X25519.AArch64.Bnd f a) (hg : VG.Proof.X25519.AArch64.Bnd g b) (ha : a ≤ 62)
    (hb : b ≤ a) : VG.Proof.X25519.AArch64.Bnd (VG.Proof.X25519.AArch64.addF f g) (a + 1) ∧ toFe (VG.Proof.X25519.AArch64.val15 (VG.Proof.X25519.AArch64.addF f g)) = toFe (VG.Proof.X25519.AArch64.val15 f) + toFe (VG.Proof.X25519.AArch64.val15 g) := by
  have e : ∀ k < 15, VG.Proof.X25519.AArch64.addF f g k = f k + g k := fun k hk => by
    have h1 := hf k hk
    have h2 := hg k hk
    have : 2 ^ b ≤ 2 ^ a := Nat.pow_le_pow_right (by decide) hb
    have : 2 ^ a ≤ 2 ^ 62 := Nat.pow_le_pow_right (by decide) ha
    simp only [VG.Proof.X25519.AArch64.addF, hk, ite_true]; exact Nat.mod_eq_of_lt (by omega)
  refine ⟨fun k hk => ?_, ?_⟩
  · have h1 := hf k hk
    have h2 := hg k hk
    have : 2 ^ b ≤ 2 ^ a := Nat.pow_le_pow_right (by decide) hb
    rw [e k hk, Nat.pow_succ]; omega
  · rw [VG.Proof.X25519.AArch64.val15, VG.Proof.X25519.AArch64.valN_congr e, VG.Proof.X25519.AArch64.valN_add]; exact toFe_add rfl

/-- The limbs of `16 p`. -/
def p16 (i : Nat) : Nat := if i = 0 then 2 ^ 21 - 304 else 2 ^ 21 - 16

theorem valN_p16 : VG.Proof.X25519.AArch64.valN VG.Proof.X25519.AArch64.p16 15 = 16 * P := by decide

/-- `x + y - z` as `add` then `sub` compute it. -/
def subL (x y z : Nat) : Nat := (2 ^ 64 - z + (x + y) % 2 ^ 64) % 2 ^ 64

/-- The difference, as `sub` computes it: `f + 16 p - g`. -/
def subF (f g : Nat → Nat) (k : Nat) : Nat := if k < 15 then VG.Proof.X25519.AArch64.subL (f k) (VG.Proof.X25519.AArch64.p16 k) (g k) else 0

theorem subF_spec {f g : Nat → Nat} {a : Nat} (hf : VG.Proof.X25519.AArch64.Bnd f a) (hg : VG.Proof.X25519.AArch64.Bnd g 20) (ha : 21 ≤ a)
    (ha' : a ≤ 62) : VG.Proof.X25519.AArch64.Bnd (VG.Proof.X25519.AArch64.subF f g) (a + 1) ∧ toFe (VG.Proof.X25519.AArch64.val15 (VG.Proof.X25519.AArch64.subF f g)) = toFe (VG.Proof.X25519.AArch64.val15 f) - toFe (VG.Proof.X25519.AArch64.val15 g) := by
  have hp : ∀ k, 2 ^ 21 - 304 ≤ VG.Proof.X25519.AArch64.p16 k ∧ VG.Proof.X25519.AArch64.p16 k ≤ 2 ^ 21 := fun k => by
    simp only [VG.Proof.X25519.AArch64.p16]; split <;> omega
  have e : ∀ k < 15, VG.Proof.X25519.AArch64.subF f g k + g k = f k + VG.Proof.X25519.AArch64.p16 k := fun k hk => by
    have h1 := hf k hk
    have h2 := hg k hk
    have h3 := hp k
    have : 2 ^ a ≤ 2 ^ 62 := Nat.pow_le_pow_right (by decide) ha'
    simp only [VG.Proof.X25519.AArch64.subF, VG.Proof.X25519.AArch64.subL, hk, ite_true]
    rw [Nat.mod_eq_of_lt (by omega : f k + p16 k < 2 ^ 64)]
    omega
  refine ⟨fun k hk => ?_, ?_⟩
  · have h1 := hf k hk
    have h3 := hp k
    have := e k hk
    have : 2 ^ 21 ≤ 2 ^ a := Nat.pow_le_pow_right (by decide) ha
    rw [Nat.pow_succ]; omega
  · refine toFe_sub ?_
    have e' : VG.Proof.X25519.AArch64.valN (fun k => VG.Proof.X25519.AArch64.subF f g k + g k) 15 = VG.Proof.X25519.AArch64.valN (fun k => f k + VG.Proof.X25519.AArch64.p16 k) 15 := VG.Proof.X25519.AArch64.valN_congr e
    rw [VG.Proof.X25519.AArch64.valN_add, VG.Proof.X25519.AArch64.valN_add, VG.Proof.X25519.AArch64.valN_p16] at e'
    rw [e', Nat.mul_comm 16 P, Nat.add_mul_mod_self_left]

end VG.Proof.X25519.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.AArch64.Codec`. -/
section

/-!
# X25519 on AArch64: decoding and encoding, as numbers

The u-coordinate's four 64-bit words cut into fifteen 17-bit limbs (the top
bit left out), and the full reduction and packing of the result.
-/

namespace VG.Proof.X25519.AArch64

open VG.Spec.X25519 VG.Proof.X25519

/-- The number of four 64-bit words. -/
def uN (w0 w1 w2 w3 : Nat) : Nat := w0 + 2 ^ 64 * w1 + 2 ^ 128 * w2 + 2 ^ 192 * w3

/-- The limbs of a number are its digits in radix `2¹⁷`. -/
theorem valN_digits (N : Nat) (n : Nat) : VG.Proof.X25519.AArch64.valN (fun i => N / 2 ^ (17 * i) % 2 ^ 17) n = N % 2 ^ (17 * n) := by
  induction n with
  | zero => simp [VG.Proof.X25519.AArch64.valN, Nat.mod_one]
  | succ n ih =>
    rw [VG.Proof.X25519.AArch64.valN, ih, show 17 * (n + 1) = 17 * n + 17 by omega, Nat.pow_add, Nat.mod_mul,
      Nat.mul_comm (N / 2 ^ (17 * n) % 2 ^ 17)]

/-- Limb `i` of the u-coordinate, as `limbOf i` computes it from the words `w`. -/
def ulimb (w : Nat → Nat) (i : Nat) : Nat :=
  if 17 * i % 64 + 17 ≤ 64 then w (17 * i / 64) / 2 ^ (17 * i % 64) % 2 ^ 17
  else (w (17 * i / 64) / 2 ^ (17 * i % 64) + w (17 * i / 64 + 1) * 2 ^ (64 - 17 * i % 64) % 2 ^ 64) % 2 ^ 64 %
    2 ^ 17

theorem ulimb_eq {w : Nat → Nat} (h0 : w 0 < 2 ^ 64) (h1 : w 1 < 2 ^ 64) (h2 : w 2 < 2 ^ 64) : ∀ i < 15, VG.Proof.X25519.AArch64.ulimb w i = VG.Proof.X25519.AArch64.uN (w 0) (w 1) (w 2) (w 3) / 2 ^ (17 * i) % 2 ^ 17 := by
  intro i hi
  simp only [VG.Proof.X25519.AArch64.uN]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨
    i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp only [VG.Proof.X25519.AArch64.ulimb, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceAdd, Nat.reduceSub,
    Nat.reducePow, Nat.reduceLeDiff, ite_true, ite_false, Nat.pow_zero, Nat.div_one] <;> omega

/-! ## The full reduction -/

/-- The carry out of `x + 19` (limbs `f`), as `quot` computes it. -/
def quotN (f : Nat → Nat) : Nat → Nat
  | 0 => (f 0 + 19) % 2 ^ 64 / 2 ^ 17
  | n + 1 => (f (n + 1) + VG.Proof.X25519.AArch64.quotN f n) % 2 ^ 64 / 2 ^ 17

/-- `19 q` added to limb 0. -/
def add19 (f : Nat → Nat) (q : Nat) (i : Nat) : Nat := if i = 0 then (f 0 + q * 19) % 2 ^ 64 else f i

/-- Limb 14 cut to 17 bits (bit 255 and above dropped). -/
def maskTop (f : Nat → Nat) (i : Nat) : Nat := if i = 14 then f 14 % 2 ^ 17 else f i

/-- The two rounds of carries of `freeze`. -/
def twice (f : Nat → Nat) : Nat → Nat := VG.Proof.X25519.AArch64.cfold (VG.Proof.X25519.AArch64.chainN (VG.Proof.X25519.AArch64.cfold (VG.Proof.X25519.AArch64.chainN f 14)) 14)

/-- The fully reduced limbs, as `freeze` computes them. -/
def freezeF (f : Nat → Nat) : Nat → Nat :=
  VG.Proof.X25519.AArch64.maskTop (VG.Proof.X25519.AArch64.chainN (VG.Proof.X25519.AArch64.add19 (VG.Proof.X25519.AArch64.twice f) (VG.Proof.X25519.AArch64.quotN (VG.Proof.X25519.AArch64.twice f) 14)) 14)

theorem valN_ge0 (f : Nat → Nat) : ∀ n, 1 ≤ n → f 0 ≤ VG.Proof.X25519.AArch64.valN f n
  | 0, h => absurd h (by decide)
  | 1, _ => by simp [VG.Proof.X25519.AArch64.valN]
  | n + 2, _ => by
    have := VG.Proof.X25519.AArch64.valN_ge0 f (n + 1) (by omega)
    rw [VG.Proof.X25519.AArch64.valN]; omega

theorem valN_le {f : Nat → Nat} : ∀ n, 1 ≤ n → (∀ i, 1 ≤ i → i < n → f i < 2 ^ 17) →
    VG.Proof.X25519.AArch64.valN f n + 2 ^ 17 ≤ f 0 + 2 ^ (17 * n)
  | 0, h, _ => absurd h (by decide)
  | 1, _, _ => by simp [VG.Proof.X25519.AArch64.valN]
  | n + 2, _, h => by
    have ih := VG.Proof.X25519.AArch64.valN_le (n + 1) (by omega) fun i h1 h2 => h i h1 (by omega)
    have hn := h (n + 1) (by omega) (by omega)
    rw [VG.Proof.X25519.AArch64.valN]
    have : f (n + 1) * 2 ^ (17 * (n + 1)) + 2 ^ (17 * (n + 1)) ≤ 2 ^ 17 * 2 ^ (17 * (n + 1)) := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hn
    rw [show 17 * (n + 2) = 17 + 17 * (n + 1) by omega, Nat.pow_add]
    omega

theorem quotN_eq {f : Nat → Nat} (hf : ∀ i < 15, f i < 2 ^ 17) :
    ∀ n < 15, VG.Proof.X25519.AArch64.quotN f n = (VG.Proof.X25519.AArch64.valN f (n + 1) + 19) / 2 ^ (17 * (n + 1)) := by
  intro n hn
  induction n with
  | zero =>
    have := hf 0 (by decide)
    simp only [VG.Proof.X25519.AArch64.quotN, VG.Proof.X25519.AArch64.valN, Nat.zero_add, Nat.mul_one, Nat.mul_zero, Nat.pow_zero, Nat.mul_one]
    rw [Nat.mod_eq_of_lt (by omega)]
  | succ n ih =>
    have h1 := ih (by omega)
    have h2 := hf (n + 1) hn
    have hv : VG.Proof.X25519.AArch64.valN f (n + 1) < 2 ^ (17 * (n + 1)) := VG.Proof.X25519.AArch64.valN_lt fun i hi => hf i (by omega)
    have hq : (VG.Proof.X25519.AArch64.valN f (n + 1) + 19) / 2 ^ (17 * (n + 1)) ≤ 1 := by
      have : 19 ≤ 2 ^ (17 * (n + 1)) :=
        Nat.le_trans (by decide) (Nat.pow_le_pow_right (by decide) (by omega : 5 ≤ 17 * (n + 1)))
      rw [Nat.div_le_iff_le_mul_add_pred (Nat.two_pow_pos _)]; omega
    rw [VG.Proof.X25519.AArch64.quotN, h1, Nat.mod_eq_of_lt (by omega),
      show VG.Proof.X25519.AArch64.valN f (n + 1 + 1) = VG.Proof.X25519.AArch64.valN f (n + 1) + f (n + 1) * 2 ^ (17 * (n + 1)) from rfl,
      show 17 * (n + 1 + 1) = 17 * (n + 1) + 17 by omega,
      Nat.pow_add, ← Nat.div_div_eq_div_mul, show VG.Proof.X25519.AArch64.valN f (n + 1) + f (n + 1) * 2 ^ (17 * (n + 1)) + 19 =
        VG.Proof.X25519.AArch64.valN f (n + 1) + 19 + f (n + 1) * 2 ^ (17 * (n + 1)) by omega,
      Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.add_comm]

theorem valN_limb0 {f g : Nat → Nat} {d : Nat} (h0 : g 0 = f 0 + d) (hi : ∀ i, 0 < i → g i = f i) :
    ∀ n, 1 ≤ n → VG.Proof.X25519.AArch64.valN g n = VG.Proof.X25519.AArch64.valN f n + d
  | 0, h => absurd h (by decide)
  | 1, _ => by simp [VG.Proof.X25519.AArch64.valN, h0]
  | n + 2, _ => by
    show VG.Proof.X25519.AArch64.valN g (n + 1) + g (n + 1) * _ = VG.Proof.X25519.AArch64.valN f (n + 1) + f (n + 1) * _ + d
    rw [VG.Proof.X25519.AArch64.valN_limb0 h0 hi (n + 1) (by omega), hi (n + 1) (by omega)]; omega

theorem valN_split (f : Nat → Nat) : VG.Proof.X25519.AArch64.valN f 15 = VG.Proof.X25519.AArch64.valN f 14 + f 14 * 2 ^ 238 := rfl

theorem maskTop_valN (f : Nat → Nat) : VG.Proof.X25519.AArch64.valN (VG.Proof.X25519.AArch64.maskTop f) 15 + 2 ^ 255 * (f 14 / 2 ^ 17) = VG.Proof.X25519.AArch64.valN f 15 := by
  rw [VG.Proof.X25519.AArch64.valN_split, VG.Proof.X25519.AArch64.valN_split, VG.Proof.X25519.AArch64.valN_congr (g := f) fun i hi => by
    simp only [VG.Proof.X25519.AArch64.maskTop, show i ≠ 14 by omega, ite_false]]
  simp only [VG.Proof.X25519.AArch64.maskTop, ite_true]
  omega

/-- `freeze`: from limbs below `2¹⁸`, the limbs of the number modulo `p`. -/
theorem freezeF_spec {f : Nat → Nat} (hf : VG.Proof.X25519.AArch64.Bnd f 18) :
    VG.Proof.X25519.AArch64.Bnd (VG.Proof.X25519.AArch64.freezeF f) 17 ∧ VG.Proof.X25519.AArch64.val15 (VG.Proof.X25519.AArch64.freezeF f) < P ∧ toFe (VG.Proof.X25519.AArch64.val15 (VG.Proof.X25519.AArch64.freezeF f)) = toFe (VG.Proof.X25519.AArch64.val15 f) := by
  show _ ∧ VG.Proof.X25519.AArch64.valN (VG.Proof.X25519.AArch64.freezeF f) 15 < P ∧ toFe (VG.Proof.X25519.AArch64.valN (VG.Proof.X25519.AArch64.freezeF f) 15) = toFe (VG.Proof.X25519.AArch64.valN f 15)
  -- the first round of carries
  obtain ⟨a1, a2, -, a4⟩ := VG.Proof.X25519.AArch64.chainN_spec (M := 2 ^ 18) (by decide) (fun i hi => Nat.le_of_lt (hf i hi))
    (n := 14) (by decide)
  generalize hg1 : VG.Proof.X25519.AArch64.chainN f 14 = g1 at a1 a2 a4
  have a0 := a1 0 (by decide)
  have hfold1 : g1 0 + g1 14 / 2 ^ 17 * 19 < 2 ^ 64 := by omega
  have v1 := VG.Proof.X25519.AArch64.cfold_val hfold1
  simp only [VG.Proof.X25519.AArch64.val15] at v1
  have p10 : VG.Proof.X25519.AArch64.cfold g1 0 = g1 0 + g1 14 / 2 ^ 17 * 19 := by
    simp only [VG.Proof.X25519.AArch64.cfold, show (0 : Nat) ≠ 14 by decide, ite_false, ite_true]; exact Nat.mod_eq_of_lt hfold1
  have p1i : ∀ i, 1 ≤ i → i < 15 → VG.Proof.X25519.AArch64.cfold g1 i < 2 ^ 17 := fun i h1 h15 => by
    simp only [VG.Proof.X25519.AArch64.cfold, show i ≠ 0 by omega]
    split
    · exact Nat.mod_lt _ (by decide)
    · simp only [ite_false]; exact a1 i (by omega)
  generalize hp1 : VG.Proof.X25519.AArch64.cfold g1 = p1 at v1 p10 p1i
  -- the second round
  obtain ⟨b1, b2, -, b4⟩ := VG.Proof.X25519.AArch64.chainN_spec (f := p1) (M := 2 ^ 17 + 37) (by decide) (fun i hi => by
    rcases Nat.eq_zero_or_pos i with rfl | h
    · omega
    · exact Nat.le_of_lt (Nat.lt_of_lt_of_le (p1i i h hi) (by decide))) (n := 14) (by decide)
  generalize hg2 : VG.Proof.X25519.AArch64.chainN p1 14 = g2 at b1 b2 b4
  have b0 := b1 0 (by decide)
  have hfold2 : g2 0 + g2 14 / 2 ^ 17 * 19 < 2 ^ 64 := by omega
  have v2 := VG.Proof.X25519.AArch64.cfold_val hfold2
  simp only [VG.Proof.X25519.AArch64.val15] at v2
  have hV1 : VG.Proof.X25519.AArch64.valN p1 15 + 2 ^ 17 ≤ p1 0 + 2 ^ (17 * 15) := VG.Proof.X25519.AArch64.valN_le 15 (by decide) fun i h1 h2 => p1i i h1 h2
  have hlow : g2 0 + g2 14 * 2 ^ 238 ≤ VG.Proof.X25519.AArch64.valN g2 15 := by
    rw [VG.Proof.X25519.AArch64.valN_split]; have := VG.Proof.X25519.AArch64.valN_ge0 g2 14 (by decide); omega
  have p20 : VG.Proof.X25519.AArch64.cfold g2 0 = g2 0 + g2 14 / 2 ^ 17 * 19 := by
    simp only [VG.Proof.X25519.AArch64.cfold, show (0 : Nat) ≠ 14 by decide, ite_false, ite_true]; exact Nat.mod_eq_of_lt hfold2
  have p2b : VG.Proof.X25519.AArch64.Bnd (VG.Proof.X25519.AArch64.cfold g2) 17 := fun i hi => by
    rcases Nat.eq_zero_or_pos i with rfl | h
    · rw [p20]
      rw [b4] at hlow
      simp only [Nat.reduceMul] at hV1
      omega
    · simp only [VG.Proof.X25519.AArch64.cfold, show i ≠ 0 by omega]
      split
      · exact Nat.mod_lt _ (by decide)
      · simp only [ite_false]; exact b1 i (by omega)
  generalize hp2 : VG.Proof.X25519.AArch64.cfold g2 = p2 at v2 p2b
  -- the carry out of `x + 19`
  have hV2 : VG.Proof.X25519.AArch64.valN p2 15 < 2 ^ 255 := VG.Proof.X25519.AArch64.valN_lt fun i hi => p2b i hi
  have hq := VG.Proof.X25519.AArch64.quotN_eq (f := p2) (fun i hi => p2b i hi) 14 (by decide)
  simp only [Nat.reduceAdd, Nat.reduceMul] at hq
  have hq1 : VG.Proof.X25519.AArch64.quotN p2 14 ≤ 1 := by rw [hq]; omega
  have hp30 : p2 0 + VG.Proof.X25519.AArch64.quotN p2 14 * 19 < 2 ^ 64 := by have := p2b 0 (by decide); omega
  have v3 : VG.Proof.X25519.AArch64.valN (VG.Proof.X25519.AArch64.add19 p2 (VG.Proof.X25519.AArch64.quotN p2 14)) 15 = VG.Proof.X25519.AArch64.valN p2 15 + VG.Proof.X25519.AArch64.quotN p2 14 * 19 :=
    VG.Proof.X25519.AArch64.valN_limb0 (by simp only [VG.Proof.X25519.AArch64.add19, ite_true]; exact Nat.mod_eq_of_lt hp30)
      (fun i hi => by simp only [VG.Proof.X25519.AArch64.add19, show i ≠ 0 by omega, ite_false]) 15 (by decide)
  obtain ⟨c1, c2, -, c4⟩ := VG.Proof.X25519.AArch64.chainN_spec (f := VG.Proof.X25519.AArch64.add19 p2 (VG.Proof.X25519.AArch64.quotN p2 14)) (M := 2 ^ 17 + 18) (by decide)
    (fun i hi => by
      simp only [VG.Proof.X25519.AArch64.add19]
      split
      · rename_i h; subst h; have := p2b 0 (by decide); rw [Nat.mod_eq_of_lt hp30]; omega
      · exact Nat.le_of_lt (Nat.lt_of_lt_of_le (p2b i hi) (by decide))) (n := 14) (by decide)
  have hr := VG.Proof.X25519.AArch64.maskTop_valN (VG.Proof.X25519.AArch64.chainN (VG.Proof.X25519.AArch64.add19 p2 (VG.Proof.X25519.AArch64.quotN p2 14)) 14)
  have rb : VG.Proof.X25519.AArch64.Bnd (VG.Proof.X25519.AArch64.freezeF f) 17 := fun i hi => by
    simp only [VG.Proof.X25519.AArch64.freezeF, VG.Proof.X25519.AArch64.twice, hg1, hp1, hg2, hp2, VG.Proof.X25519.AArch64.maskTop]
    split
    · exact Nat.mod_lt _ (by decide)
    · exact c1 i (by omega)
  have hR : VG.Proof.X25519.AArch64.valN (VG.Proof.X25519.AArch64.freezeF f) 15 < 2 ^ 255 := VG.Proof.X25519.AArch64.valN_lt fun i hi => rb i hi
  have hF : VG.Proof.X25519.AArch64.freezeF f = VG.Proof.X25519.AArch64.maskTop (VG.Proof.X25519.AArch64.chainN (VG.Proof.X25519.AArch64.add19 p2 (VG.Proof.X25519.AArch64.quotN p2 14)) 14) := by
    simp only [VG.Proof.X25519.AArch64.freezeF, VG.Proof.X25519.AArch64.twice, hg1, hp1, hg2, hp2]
  rw [← hF, c4, v3] at hr
  have c14 : VG.Proof.X25519.AArch64.chainN (VG.Proof.X25519.AArch64.add19 p2 (VG.Proof.X25519.AArch64.quotN p2 14)) 14 14 / 2 ^ 17 ≤ 1 := by omega_using [c2]
  have hP : P = 2 ^ 255 - 19 := rfl
  have e1 : VG.Proof.X25519.AArch64.valN (VG.Proof.X25519.AArch64.freezeF f) 15 + P * VG.Proof.X25519.AArch64.quotN p2 14 = VG.Proof.X25519.AArch64.valN p2 15 := by
    rw [hP]; omega_using [hr, hq, hV2, hR, c14]
  have e2 : VG.Proof.X25519.AArch64.valN (VG.Proof.X25519.AArch64.freezeF f) 15 < P := by
    rcases (by omega_using [hq1] : quotN p2 14 = 0 ∨ quotN p2 14 = 1) with h | h
    · rw [h] at e1 hq
      rw [hP]; omega_using [e1, hq]
    · rw [h] at e1
      rw [hP] at e1 ⊢; omega_using [e1, hV2]
  refine ⟨rb, e2, ?_⟩
  have t1 : toFe (VG.Proof.X25519.AArch64.valN p2 15) = toFe (VG.Proof.X25519.AArch64.valN f 15) := by
    rw [v2, b4, v1, a4]
  rw [← t1]
  refine toFe_congr ?_
  rw [← e1, Nat.add_mul_mod_self_left]

/-! ## Packing -/

/-- Limb `i` shifted to its place in word `j`, as `place` computes it. -/
def placeV (l : Nat → Nat) (i j : Nat) : Nat :=
  if 64 * j ≤ 17 * i then l i * 2 ^ (17 * i - 64 * j) % 2 ^ 64 else l i / 2 ^ (64 * j - 17 * i)

/-- Word `j`, as `packWord j` computes it. -/
def packV (l : Nat → Nat) (j : Nat) : Nat :=
  match Impl.X25519.AArch64.wordLimbs j with
  | [] => 0
  | i :: is => is.foldl (fun acc i => (acc + VG.Proof.X25519.AArch64.placeV l i j) % 2 ^ 64) (VG.Proof.X25519.AArch64.placeV l i j)

theorem shl_mod (x : Nat) {k : Nat} (hk : k ≤ 64) : x * 2 ^ k % 2 ^ 64 = x % 2 ^ (64 - k) * 2 ^ k := by
  rw [show 2 ^ 64 = 2 ^ (64 - k) * 2 ^ k by rw [← Nat.pow_add, Nat.sub_add_cancel hk],
    Nat.mul_mod_mul_right]

theorem mod64_of_lt {x : Nat} (h : x < 2 ^ 64) : x % 2 ^ 64 = x := Nat.mod_eq_of_lt h

theorem packV_words {l : Nat → Nat} (hl : VG.Proof.X25519.AArch64.Bnd l 17) :
    VG.Proof.X25519.AArch64.packV l 0 = l 0 + l 1 * 2 ^ 17 + l 2 * 2 ^ 34 + l 3 % 2 ^ 13 * 2 ^ 51 ∧
    VG.Proof.X25519.AArch64.packV l 1 = l 3 / 2 ^ 13 + l 4 * 2 ^ 4 + l 5 * 2 ^ 21 + l 6 * 2 ^ 38 + l 7 % 2 ^ 9 * 2 ^ 55 ∧
    VG.Proof.X25519.AArch64.packV l 2 = l 7 / 2 ^ 9 + l 8 * 2 ^ 8 + l 9 * 2 ^ 25 + l 10 * 2 ^ 42 + l 11 % 2 ^ 5 * 2 ^ 59 ∧
    VG.Proof.X25519.AArch64.packV l 3 = l 11 / 2 ^ 5 + l 12 * 2 ^ 12 + l 13 * 2 ^ 29 + l 14 * 2 ^ 46 := by
  have h0 := hl 0 (by decide); have h1 := hl 1 (by decide); have h2 := hl 2 (by decide)
  have h3 := hl 3 (by decide); have h4 := hl 4 (by decide); have h5 := hl 5 (by decide)
  have h6 := hl 6 (by decide); have h7 := hl 7 (by decide); have h8 := hl 8 (by decide)
  have h9 := hl 9 (by decide); have h10 := hl 10 (by decide); have h11 := hl 11 (by decide)
  have h12 := hl 12 (by decide); have h13 := hl 13 (by decide); have h14 := hl 14 (by decide)
  have w0 : Impl.X25519.AArch64.wordLimbs 0 = [0, 1, 2, 3] := by decide
  have w1 : Impl.X25519.AArch64.wordLimbs 1 = [3, 4, 5, 6, 7] := by decide
  have w2 : Impl.X25519.AArch64.wordLimbs 2 = [7, 8, 9, 10, 11] := by decide
  have w3 : Impl.X25519.AArch64.wordLimbs 3 = [11, 12, 13, 14] := by decide
  have e0 : VG.Proof.X25519.AArch64.packV l 0 = (((VG.Proof.X25519.AArch64.placeV l 0 0 + VG.Proof.X25519.AArch64.placeV l 1 0) % 2 ^ 64 + VG.Proof.X25519.AArch64.placeV l 2 0) % 2 ^ 64 +
      VG.Proof.X25519.AArch64.placeV l 3 0) % 2 ^ 64 := by
    unfold VG.Proof.X25519.AArch64.packV; rw [w0]; dsimp only; rw [List.foldl_cons, List.foldl_cons, List.foldl_cons, List.foldl_nil]
  have e1 : VG.Proof.X25519.AArch64.packV l 1 = ((((VG.Proof.X25519.AArch64.placeV l 3 1 + VG.Proof.X25519.AArch64.placeV l 4 1) % 2 ^ 64 + VG.Proof.X25519.AArch64.placeV l 5 1) % 2 ^ 64 +
      VG.Proof.X25519.AArch64.placeV l 6 1) % 2 ^ 64 + VG.Proof.X25519.AArch64.placeV l 7 1) % 2 ^ 64 := by
    unfold VG.Proof.X25519.AArch64.packV; rw [w1]; dsimp only
    rw [List.foldl_cons, List.foldl_cons, List.foldl_cons, List.foldl_cons, List.foldl_nil]
  have e2 : VG.Proof.X25519.AArch64.packV l 2 = ((((VG.Proof.X25519.AArch64.placeV l 7 2 + VG.Proof.X25519.AArch64.placeV l 8 2) % 2 ^ 64 + VG.Proof.X25519.AArch64.placeV l 9 2) % 2 ^ 64 +
      VG.Proof.X25519.AArch64.placeV l 10 2) % 2 ^ 64 + VG.Proof.X25519.AArch64.placeV l 11 2) % 2 ^ 64 := by
    unfold VG.Proof.X25519.AArch64.packV; rw [w2]; dsimp only
    rw [List.foldl_cons, List.foldl_cons, List.foldl_cons, List.foldl_cons, List.foldl_nil]
  have e3 : VG.Proof.X25519.AArch64.packV l 3 = (((VG.Proof.X25519.AArch64.placeV l 11 3 + VG.Proof.X25519.AArch64.placeV l 12 3) % 2 ^ 64 + VG.Proof.X25519.AArch64.placeV l 13 3) % 2 ^ 64 +
      VG.Proof.X25519.AArch64.placeV l 14 3) % 2 ^ 64 := by
    unfold VG.Proof.X25519.AArch64.packV; rw [w3]; dsimp only; rw [List.foldl_cons, List.foldl_cons, List.foldl_cons, List.foldl_nil]
  rw [e0, e1, e2, e3]
  simp only [VG.Proof.X25519.AArch64.placeV, Nat.reduceMul, Nat.reduceLeDiff, ite_true, ite_false, Nat.reduceSub, Nat.pow_zero,
    Nat.mul_one]
  rw [VG.Proof.X25519.AArch64.shl_mod (l 3) (k := 51) (by decide), VG.Proof.X25519.AArch64.shl_mod (l 7) (k := 55) (by decide),
    VG.Proof.X25519.AArch64.shl_mod (l 11) (k := 59) (by decide)]
  simp only [Nat.reduceSub]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  simp (disch := omega) only [VG.Proof.X25519.AArch64.mod64_of_lt]

theorem digits4 {w0 w1 w2 w3 : Nat} (h0 : w0 < 2 ^ 64) (h1 : w1 < 2 ^ 64) (h2 : w2 < 2 ^ 64)
    (h3 : w3 < 2 ^ 64) : ∀ j < 4, (w0 + 2 ^ 64 * w1 + 2 ^ 128 * w2 + 2 ^ 192 * w3) / 2 ^ (64 * j) % 2 ^ 64 =
      [w0, w1, w2, w3].getD j 0 := by
  intro j hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
  · simp only [List.getD_cons_zero]; omega
  · simp only [List.getD_cons_succ, List.getD_cons_zero]; omega
  · simp only [List.getD_cons_succ, List.getD_cons_zero]; omega
  · simp only [List.getD_cons_succ, List.getD_cons_zero]; omega

theorem packV_eq {l : Nat → Nat} (hl : VG.Proof.X25519.AArch64.Bnd l 17) : ∀ j < 4, VG.Proof.X25519.AArch64.packV l j = VG.Proof.X25519.AArch64.valN l 15 / 2 ^ (64 * j) % 2 ^ 64 := by
  obtain ⟨w0, w1, w2, w3⟩ := VG.Proof.X25519.AArch64.packV_words hl
  have h0 := hl 0 (by decide); have h1 := hl 1 (by decide); have h2 := hl 2 (by decide)
  have h3 := hl 3 (by decide); have h4 := hl 4 (by decide); have h5 := hl 5 (by decide)
  have h6 := hl 6 (by decide); have h7 := hl 7 (by decide); have h8 := hl 8 (by decide)
  have h9 := hl 9 (by decide); have h10 := hl 10 (by decide); have h11 := hl 11 (by decide)
  have h12 := hl 12 (by decide); have h13 := hl 13 (by decide); have h14 := hl 14 (by decide)
  have b0 : VG.Proof.X25519.AArch64.packV l 0 < 2 ^ 64 := by rw [w0]; omega_using [h0, h1, h2]
  have b1 : VG.Proof.X25519.AArch64.packV l 1 < 2 ^ 64 := by rw [w1]; omega_using [h3, h4, h5, h6]
  have b2 : VG.Proof.X25519.AArch64.packV l 2 < 2 ^ 64 := by rw [w2]; omega_using [h7, h8, h9, h10]
  have b3 : VG.Proof.X25519.AArch64.packV l 3 < 2 ^ 64 := by rw [w3]; omega_using [h11, h12, h13, h14]
  have e3 : l 3 * 2 ^ 51 = l 3 % 2 ^ 13 * 2 ^ 51 + 2 ^ 64 * (l 3 / 2 ^ 13) := by
    conv => lhs; rw [← Nat.div_add_mod (l 3) (2 ^ 13)]
    grind
  have e7 : l 7 * 2 ^ 119 = 2 ^ 64 * (l 7 % 2 ^ 9 * 2 ^ 55) + 2 ^ 128 * (l 7 / 2 ^ 9) := by
    conv => lhs; rw [← Nat.div_add_mod (l 7) (2 ^ 9)]
    grind
  have e11 : l 11 * 2 ^ 187 = 2 ^ 128 * (l 11 % 2 ^ 5 * 2 ^ 59) + 2 ^ 192 * (l 11 / 2 ^ 5) := by
    conv => lhs; rw [← Nat.div_add_mod (l 11) (2 ^ 5)]
    grind
  have hv : VG.Proof.X25519.AArch64.valN l 15 = VG.Proof.X25519.AArch64.packV l 0 + 2 ^ 64 * VG.Proof.X25519.AArch64.packV l 1 + 2 ^ 128 * VG.Proof.X25519.AArch64.packV l 2 + 2 ^ 192 * VG.Proof.X25519.AArch64.packV l 3 := by
    rw [w0, w1, w2, w3]
    simp only [VG.Proof.X25519.AArch64.valN, Nat.reduceMul, Nat.pow_zero, Nat.mul_one, Nat.zero_add]
    rw [e3, e7, e11]
    grind
  intro j hj
  rw [hv, VG.Proof.X25519.AArch64.digits4 b0 b1 b2 b3 j hj]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
    simp only [List.getD_cons_succ, List.getD_cons_zero]

end VG.Proof.X25519.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.AArch64.Ops`. -/
section

/-!
# X25519 on AArch64: the steps of the field operations

The field operations read and write words of the working space (`x3`, 4096
bytes) at constant offsets; each lemma here runs a few instructions and states
their effect on the numbers in the registers and in the words of the working
space.
-/

namespace VG.Proof.X25519.AArch64

open VG VG.AArch64 VG.Impl.X25519.AArch64

/-- The value of a register, as a number. -/
abbrev v (s : State) (r : Reg) : Nat := (s.gpr r).toNat

/-- The 64-bit word at `b + off`, as a number. -/
def wd (m : Mem) (b : Addr) (off : Nat) : Nat := (m.readW (b + BitVec.ofNat 64 off) 64).toNat

/-- The working space at `b`. -/
abbrev scR (b : Addr) : Region := ⟨b, 4096⟩

/-- The working space is at `b`, in `x3`, and writable. -/
structure Sc (b : Addr) (s : State) : Prop where
  x3 : s.gpr .x3 = b
  wr : VG.Proof.X25519.AArch64.scR b ∈ s.wr

/-- The registers but `W` are unchanged, and so are the regions. -/
structure Kp (W : List Reg) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ W → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Kp.refl (W : List Reg) (s : State) : VG.Proof.X25519.AArch64.Kp W s s := ⟨fun _ _ => rfl, rfl, rfl⟩

theorem Kp.trans {W W' : List Reg} {s₁ s₂ s₃ : State} (h₁ : VG.Proof.X25519.AArch64.Kp W s₁ s₂) (h₂ : VG.Proof.X25519.AArch64.Kp W' s₂ s₃) :
    VG.Proof.X25519.AArch64.Kp (W ++ W') s₁ s₃ :=
  ⟨fun r hr => by
    rw [List.mem_append, not_or] at hr
    rw [h₂.gpr r hr.2, h₁.gpr r hr.1], h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr⟩

theorem Kp.mono {W W' : List Reg} {s s' : State} (h : VG.Proof.X25519.AArch64.Kp W s s') (hs : ∀ r ∈ W, r ∈ W') :
    VG.Proof.X25519.AArch64.Kp W' s s' :=
  ⟨fun r hr => h.gpr r fun h' => hr (hs r h'), h.rd, h.wr⟩

theorem Kp.sub {W W' : List Reg} {s s' : State} (h : VG.Proof.X25519.AArch64.Kp W s s') (hs : W ⊆ W') : VG.Proof.X25519.AArch64.Kp W' s s' :=
  h.mono fun _ hr => hs hr

/-- Closes `W ⊆ W'` for lists of registers, some of them variables. -/
macro "sub_regs" : tactic => `(tactic| simp only [List.cons_subset, List.append_subset, List.nil_subset,
  List.mem_cons, List.mem_append, true_or, or_true, and_true, List.not_mem_nil, or_false, and_self,
  List.cons_append, List.nil_append])

theorem Sc.of_kp {b : Addr} {W : List Reg} {s s' : State} (hs : VG.Proof.X25519.AArch64.Sc b s) (h : VG.Proof.X25519.AArch64.Kp W s s')
    (hW : Reg.x3 ∉ W) : VG.Proof.X25519.AArch64.Sc b s' :=
  ⟨by rw [h.gpr _ hW, hs.x3], by rw [h.wr]; exact hs.wr⟩

theorem Sc.mem {b : Addr} {s : State} (hs : VG.Proof.X25519.AArch64.Sc b s) (m : Mem) : VG.Proof.X25519.AArch64.Sc b { s with
                                                                              mem := m } :=
  ⟨hs.x3, hs.wr⟩

/-- An offset of a word in the working space. -/
def Off (off : Nat) : Prop := off % 8 = 0 ∧ off + 8 ≤ 4096

instance (off : Nat) : Decidable (VG.Proof.X25519.AArch64.Off off) := by unfold VG.Proof.X25519.AArch64.Off; infer_instance

/-! ## Registers after writes -/

section
variable (s : State)

theorem read_x (r : Reg) : s.read .x r = s.gpr r := by
  simp only [State.read, BitVec.setWidth_eq]

theorem gpr_wx (d : Reg) (x : BitVec 64) (r : Reg) :
    (s.write .x d x).gpr r = if r = d then x else s.gpr r := by
  simp only [State.write, BitVec.setWidth_eq]

theorem gpr_wx_self (d : Reg) (x : BitVec 64) : (s.write .x d x).gpr d = x := by
  simp only [VG.Proof.X25519.AArch64.gpr_wx, ite_true]

theorem gpr_wx_ne {d r : Reg} (x : BitVec 64) (h : r ≠ d) : (s.write .x d x).gpr r = s.gpr r := by
  simp only [VG.Proof.X25519.AArch64.gpr_wx, h, ite_false]

theorem gpr_ww_self (d : Reg) (x : BitVec 32) : (s.write .w d x).gpr d = x.setWidth 64 := by
  simp only [State.write, ite_true]

theorem gpr_ww_ne {d r : Reg} (x : BitVec 32) (h : r ≠ d) : (s.write .w d x).gpr r = s.gpr r := by
  simp only [State.write, h, ite_false]

theorem mem_ww (d : Reg) (x : BitVec 32) : (s.write .w d x).mem = s.mem := rfl

theorem kp_ww (d : Reg) (x : BitVec 32) : VG.Proof.X25519.AArch64.Kp [d] s (s.write .w d x) :=
  ⟨fun r hr => VG.Proof.X25519.AArch64.gpr_ww_ne s x (by simpa using hr), rfl, rfl⟩

theorem sc_ww {b : Addr} {d : Reg} (x : BitVec 32) (hs : VG.Proof.X25519.AArch64.Sc b s) (hd : d ≠ .x3) :
    VG.Proof.X25519.AArch64.Sc b (s.write .w d x) :=
  ⟨by rw [VG.Proof.X25519.AArch64.gpr_ww_ne s x (Ne.symm hd), hs.x3], hs.wr⟩

theorem mem_wx (d : Reg) (x : BitVec 64) : (s.write .x d x).mem = s.mem := rfl
theorem rd_wx (d : Reg) (x : BitVec 64) : (s.write .x d x).rd = s.rd := rfl
theorem wr_wx (d : Reg) (x : BitVec 64) : (s.write .x d x).wr = s.wr := rfl

theorem kp_wx (d : Reg) (x : BitVec 64) : VG.Proof.X25519.AArch64.Kp [d] s (s.write .x d x) :=
  ⟨fun r hr => VG.Proof.X25519.AArch64.gpr_wx_ne s x (by simpa using hr), rfl, rfl⟩

theorem sc_wx {b : Addr} {d : Reg} (x : BitVec 64) (hs : VG.Proof.X25519.AArch64.Sc b s) (hd : d ≠ .x3) :
    VG.Proof.X25519.AArch64.Sc b (s.write .x d x) :=
  ⟨by rw [VG.Proof.X25519.AArch64.gpr_wx_ne s x (Ne.symm hd), hs.x3], hs.wr⟩

end

/-! ## Instructions -/

theorem off_in {b : Addr} {s : State} (hs : VG.Proof.X25519.AArch64.Sc b s) {off : Nat} (ho : VG.Proof.X25519.AArch64.Off off) :
    InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 off) 8 :=
  ⟨VG.Proof.X25519.AArch64.scR b, hs.wr, by rw [hs.x3]; exact Offset.contains_base b ho.2 (by have := ho.2; omega)⟩

theorem exec_ld {b : Addr} {s : State} (hs : VG.Proof.X25519.AArch64.Sc b s) (t : Reg) {off : Nat} (ho : VG.Proof.X25519.AArch64.Off off) :
    exec (ld t off) s = some (s.write .x t (s.mem.readW (b + BitVec.ofNat 64 off) 64)) := by
  have h := VG.Proof.X25519.AArch64.off_in hs ho
  rw [ld, exec_ldr_x ⟨ho.1, by have := ho.2; omega⟩ (by
    obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_right _ hr, hc⟩), hs.x3]

theorem exec_st {b : Addr} {s : State} (hs : VG.Proof.X25519.AArch64.Sc b s) (t : Reg) {off : Nat} (ho : VG.Proof.X25519.AArch64.Off off) :
    exec (st t off) s = some { s with mem := s.mem.writeW (b + BitVec.ofNat 64 off) (s.gpr t) } := by
  rw [st, exec_str_x ⟨ho.1, by have := ho.2; omega⟩ (VG.Proof.X25519.AArch64.off_in hs ho), hs.x3]

theorem exec_madd_x {s : State} {d n m a : Reg} :
    exec (.madd .x d n m a) s = some (s.write .x d (s.gpr a + s.gpr n * s.gpr m)) := by
  simp only [exec, VG.Proof.X25519.AArch64.read_x]

theorem exec_mul_x {s : State} {d n m : Reg} :
    exec (.mul .x d n m) s = some (s.write .x d (s.gpr n * s.gpr m)) := by
  simp only [exec, VG.Proof.X25519.AArch64.read_x]

theorem exec_add_x {s : State} {d n m : Reg} :
    exec (.add .x d n m) s = some (s.write .x d (s.gpr n + s.gpr m)) := by
  simp only [exec, VG.Proof.X25519.AArch64.read_x]

theorem exec_sub_x {s : State} {d n m : Reg} :
    exec (.sub .x d n m) s = some (s.write .x d (s.gpr n - s.gpr m)) := by
  simp only [exec, VG.Proof.X25519.AArch64.read_x]

theorem exec_and_x {s : State} {d n m : Reg} :
    exec (.logic .and .x d n m) s = some (s.write .x d (s.gpr n &&& s.gpr m)) := by
  simp only [exec, VG.Proof.X25519.AArch64.read_x]

theorem exec_eor_x {s : State} {d n m : Reg} :
    exec (.logic .eor .x d n m) s = some (s.write .x d (s.gpr n ^^^ s.gpr m)) := by
  simp only [exec, VG.Proof.X25519.AArch64.read_x]

theorem exec_lsr {s : State} {d n : Reg} {sh : Nat} (h : sh < 64) :
    exec (.lsr .x d n sh) s = some (s.write .x d (s.gpr n >>> sh)) := by
  simp only [exec, Size.bits, h, ite_true, VG.Proof.X25519.AArch64.read_x]

theorem exec_lsl {s : State} {d n : Reg} {sh : Nat} (h : sh < 64) :
    exec (.lsl .x d n sh) s = some (s.write .x d (s.gpr n <<< sh)) := by
  simp only [exec, Size.bits, h, ite_true, VG.Proof.X25519.AArch64.read_x]

theorem exec_movz {s : State} {d : Reg} {imm : BitVec 16} :
    exec (.movz .x d imm 0) s = some (s.write .x d (imm.setWidth 64)) := by
  simp only [exec, Size.bits, Nat.mul_zero, show (0 : Nat) < 64 from by decide, ite_true,
    BitVec.shiftLeft_zero]

theorem exec_movk1 {s : State} {d : Reg} {imm : BitVec 16} :
    exec (.movk .x d imm 1) s = some (s.write .x d
      ((s.gpr d &&& ~~~((0xFFFF : BitVec 64) <<< 16)) ||| (imm.setWidth 64 <<< 16))) := by
  simp only [exec, Size.bits, Nat.mul_one, show (16 : Nat) < 64 from by decide, ite_true, VG.Proof.X25519.AArch64.read_x]

theorem exec_ldrb {s : State} {t n : Reg} {off : Nat} (ho : off < 4096)
    (h : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 1) :
    exec (.ldrb t n off) s = some (s.write .w t ((s.mem.read (s.gpr n + BitVec.ofNat 64 off) 1).setWidth 32)) := by
  simp only [exec, addr, Nat.mod_one, ho, true_and, ite_true, Option.bind_some,
    State.load, h, Option.map_some]

theorem exec_strb {s : State} {t n : Reg} {off : Nat} (ho : off < 4096)
    (h : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) 1) :
    exec (.strb t n off) s =
      some { s with mem := s.mem.write (s.gpr n + BitVec.ofNat 64 off) 1 ((s.read .w t).setWidth 8) } := by
  simp only [exec, addr, Nat.mod_one, show off < 4096 * 1 by omega, true_and, ite_true, Option.bind_some,
    State.store, h]

theorem read1_toNat (m : Mem) (a : Addr) : ((m.read a 1).setWidth 32).setWidth 64 = (m a).setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, Mem.read, BitVec.toNat_append, show (0#0).toNat = 0 from rfl,
    Nat.zero_shiftLeft, Nat.zero_or]
  have := (m a).isLt
  omega

/-! ## Numbers -/

theorem madd_toNat (a b c : BitVec 64) :
    (a + b * c).toNat = (a.toNat + b.toNat * c.toNat) % 2 ^ 64 := by
  rw [BitVec.toNat_add, BitVec.toNat_mul, Nat.add_mod_mod]

theorem lsr_toNat (a : BitVec 64) (n : Nat) : (a >>> n).toNat = a.toNat / 2 ^ n := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem lsl_toNat (a : BitVec 64) (n : Nat) : (a <<< n).toNat = a.toNat * 2 ^ n % 2 ^ 64 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

theorem and_mask17 (a b : BitVec 64) (hb : b = 0x1ffff) : (a &&& b).toNat = a.toNat % 2 ^ 17 := by
  rw [hb, BitVec.toNat_and, show (0x1ffff : BitVec 64).toNat = 2 ^ 17 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

theorem wd_def (m : Mem) (b : Addr) (off : Nat) :
    (m.readW (b + BitVec.ofNat 64 off) 64).toNat = VG.Proof.X25519.AArch64.wd m b off := rfl

/-! ## Multiply-accumulate -/

theorem not_mem3 {a b c d : Reg} (h1 : a ≠ b) (h2 : a ≠ c) (h3 : a ≠ d) : a ∉ [b, c, d] := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h1, h2, h3⟩

theorem mac_ok {b : Addr} {s : State} (hs : VG.Proof.X25519.AArch64.Sc b s) {d : Reg} {oa ob : Nat} (hd17 : d ≠ .x17)
    (hd19 : d ≠ .x19) (hoa : VG.Proof.X25519.AArch64.Off oa) (hob : VG.Proof.X25519.AArch64.Off ob) :
    WP isa (.block (mac d oa ob)) s fun s' =>
      VG.Proof.X25519.AArch64.v s' d = (VG.Proof.X25519.AArch64.v s d + VG.Proof.X25519.AArch64.wd s.mem b oa * VG.Proof.X25519.AArch64.wd s.mem b ob) % 2 ^ 64 ∧ VG.Proof.X25519.AArch64.Kp [.x17, .x19, d] s s' ∧
        s'.mem = s.mem := by
  apply WP.of_runBlock
  have hs1 := VG.Proof.X25519.AArch64.sc_wx s (s.mem.readW (b + BitVec.ofNat 64 oa) 64) hs (show Reg.x17 ≠ .x3 by decide)
  simp only [mac, runBlock_cons, VG.Proof.X25519.AArch64.exec_ld hs _ hoa, runStep_some, VG.Proof.X25519.AArch64.exec_ld hs1 _ hob, VG.Proof.X25519.AArch64.mem_wx,
    VG.Proof.X25519.AArch64.exec_madd_x, runBlock_nil, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl⟩, trivial⟩
  · simp only [VG.Proof.X25519.AArch64.v, VG.Proof.X25519.AArch64.gpr_wx_self, VG.Proof.X25519.AArch64.madd_toNat, VG.Proof.X25519.AArch64.gpr_wx_ne _ _ hd19, VG.Proof.X25519.AArch64.gpr_wx_ne _ _ hd17,
      VG.Proof.X25519.AArch64.gpr_wx_ne _ _ (show Reg.x17 ≠ .x19 by decide), VG.Proof.X25519.AArch64.wd_def]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [VG.Proof.X25519.AArch64.gpr_wx_ne _ _ hr.2.2, VG.Proof.X25519.AArch64.gpr_wx_ne _ _ hr.2.1, VG.Proof.X25519.AArch64.gpr_wx_ne _ _ hr.1]

/-- A chain of `mac`s. -/
theorem macs_ok {b : Addr} {d : Reg} (hd17 : d ≠ .x17) (hd19 : d ≠ .x19) (hd3 : d ≠ .x3) :
    ∀ (L : List (Nat × Nat)) (s : State), VG.Proof.X25519.AArch64.Sc b s → (∀ p ∈ L, VG.Proof.X25519.AArch64.Off p.1 ∧ VG.Proof.X25519.AArch64.Off p.2) →
    WP isa (.block (macs d L)) s fun s' =>
      VG.Proof.X25519.AArch64.v s' d = (VG.Proof.X25519.AArch64.v s d + (L.map fun p => VG.Proof.X25519.AArch64.wd s.mem b p.1 * VG.Proof.X25519.AArch64.wd s.mem b p.2).sum) % 2 ^ 64 ∧
        VG.Proof.X25519.AArch64.Kp [.x17, .x19, d] s s' ∧ s'.mem = s.mem
  | [], s, _, _ => by
    refine WP.block_nil ⟨?_, Kp.refl _ _, rfl⟩
    simp only [List.map_nil, List.sum_nil, Nat.add_zero]
    exact (Nat.mod_eq_of_lt (s.gpr d).isLt).symm
  | p :: L, s, hs, hL => by
    obtain ⟨h1, h2⟩ := hL p List.mem_cons_self
    rw [macs, List.flatMap_cons]
    refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.mac_ok hs hd17 hd19 h1 h2) fun s₁ ⟨e₁, k₁, m₁⟩ => ?_)
    have hs₁ := hs.of_kp k₁ (VG.Proof.X25519.AArch64.not_mem3 (by decide) (by decide) (Ne.symm hd3))
    refine WP.mono (VG.Proof.X25519.AArch64.macs_ok hd17 hd19 hd3 L s₁ hs₁ fun q hq => hL q (List.mem_cons_of_mem _ hq))
      fun s₂ ⟨e₂, k₂, m₂⟩ => ⟨?_, (k₁.trans k₂).mono fun r hr => ?_, m₂.trans m₁⟩
    · rw [e₂, m₁, e₁, List.map_cons, List.sum_cons, Nat.mod_add_mod, Nat.add_assoc]
    · exact (List.mem_append.mp hr).elim id id

/-- A sum over `List.range` as `sumR`. -/
theorem sum_range_list (t : Nat → Nat) (n : Nat) :
    ((List.range n).map t).sum = VG.Proof.X25519.AArch64.sumR t n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, VG.Proof.X25519.AArch64.sumR]; simp

/-- The limbs of the element at `b + o`. -/
def limbs (m : Mem) (b : Addr) (o : Nat) (i : Nat) : Nat := if i < 15 then VG.Proof.X25519.AArch64.wd m b (o + 8 * i) else 0

/-- An element's offset: its fifteen words are in the working space. -/
def Slot (o : Nat) : Prop := o % 8 = 0 ∧ o + 120 ≤ 4096

instance (o : Nat) : Decidable (VG.Proof.X25519.AArch64.Slot o) := by unfold VG.Proof.X25519.AArch64.Slot; infer_instance

theorem Slot.off {o : Nat} (h : VG.Proof.X25519.AArch64.Slot o) {i : Nat} (hi : i < 15) : VG.Proof.X25519.AArch64.Off (o + 8 * i) :=
  ⟨by have := h.1; omega, by have := h.2; omega⟩

theorem dreg_facts : ∀ k < 15, dreg k ≠ .x17 ∧ dreg k ≠ .x19 ∧ dreg k ≠ .x20 ∧ dreg k ≠ .x21 ∧
    dreg k ≠ .x22 ∧ dreg k ≠ .x3 ∧ dreg k ≠ .x0 ∧ dreg k ≠ .x23 ∧ dreg k ≠ .x24 := by decide

theorem dreg_inj : ∀ j < 15, ∀ k < 15, dreg j = dreg k → j = k := by decide

theorem dreg_mem : ∀ k < 15, dreg k ∈ DR := by decide

/-- Column `k` of the product of the elements at `a` and `c`. -/
theorem col_ok {b : Addr} {s : State} (hs : VG.Proof.X25519.AArch64.Sc b s) (h19 : s.gpr .x21 = 19) {a c k : Nat}
    (ha : VG.Proof.X25519.AArch64.Slot a) (hc : VG.Proof.X25519.AArch64.Slot c) (hk : k < 15) :
    WP isa (.block (col a c k)) s fun s' =>
      VG.Proof.X25519.AArch64.v s' (dreg k) = VG.Proof.X25519.AArch64.colM (VG.Proof.X25519.AArch64.limbs s.mem b a) (VG.Proof.X25519.AArch64.limbs s.mem b c) k ∧
        VG.Proof.X25519.AArch64.Kp [.x17, .x19, .x20, dreg k] s s' ∧ s'.mem = s.mem := by
  obtain ⟨d17, d19, d20, d21, -, d3, -⟩ := VG.Proof.X25519.AArch64.dreg_facts k hk
  have hlo : ∀ p ∈ loPairs a c k, VG.Proof.X25519.AArch64.Off p.1 ∧ VG.Proof.X25519.AArch64.Off p.2 := fun p hp => by
    simp only [loPairs, List.mem_map, List.mem_range] at hp
    obtain ⟨i, hi, rfl⟩ := hp
    exact ⟨ha.off (by omega), hc.off (by omega)⟩
  have hhi : ∀ p ∈ hiPairs a c k, VG.Proof.X25519.AArch64.Off p.1 ∧ VG.Proof.X25519.AArch64.Off p.2 := fun p hp => by
    simp only [hiPairs, List.mem_map, List.mem_range] at hp
    obtain ⟨j, hj, rfl⟩ := hp
    exact ⟨ha.off (by omega), hc.off (by omega)⟩
  rw [col]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.X25519.AArch64.exec_movz, ?_⟩
  have hs₀ := VG.Proof.X25519.AArch64.sc_wx s ((0 : BitVec 16).setWidth 64) hs d3
  refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.macs_ok d17 d19 d3 _ _ hs₀ hlo) fun s₁ ⟨e₁, k₁, m₁⟩ => ?_)
  have hs₁ := hs₀.of_kp k₁ (VG.Proof.X25519.AArch64.not_mem3 (by decide) (by decide) (Ne.symm d3))
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.X25519.AArch64.exec_movz, ?_⟩
  have hs₂ := VG.Proof.X25519.AArch64.sc_wx s₁ ((0 : BitVec 16).setWidth 64) hs₁ (show Reg.x20 ≠ .x3 by decide)
  refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.macs_ok (d := .x20) (by decide) (by decide) (by decide) _ _ hs₂ hhi)
    fun s₃ ⟨e₃, k₃, m₃⟩ => ?_)
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.X25519.AArch64.exec_madd_x, WP.block_nil ⟨?_, ?_, ?_⟩⟩
  · have g1 : s₃.gpr (dreg k) = s₁.gpr (dreg k) := by
      rw [k₃.gpr _ (VG.Proof.X25519.AArch64.not_mem3 d17 d19 d20), VG.Proof.X25519.AArch64.gpr_wx_ne _ _ d20]
    have g2 : s₃.gpr .x21 = 19 := by
      rw [k₃.gpr _ (by decide), VG.Proof.X25519.AArch64.gpr_wx_ne _ _ (by decide),
        k₁.gpr _ (VG.Proof.X25519.AArch64.not_mem3 (by decide) (by decide) (Ne.symm d21)), VG.Proof.X25519.AArch64.gpr_wx_ne _ _ (Ne.symm d21), h19]
    have M1 : s₁.mem = s.mem := by rw [m₁, VG.Proof.X25519.AArch64.mem_wx]
    simp only [VG.Proof.X25519.AArch64.v, VG.Proof.X25519.AArch64.gpr_wx_self, VG.Proof.X25519.AArch64.madd_toNat, g1, g2]
    simp only [VG.Proof.X25519.AArch64.v, VG.Proof.X25519.AArch64.gpr_wx_self, VG.Proof.X25519.AArch64.mem_wx, M1] at e₁ e₃
    rw [e₃, e₁, VG.Proof.X25519.AArch64.colM, VG.Proof.X25519.AArch64.lo, VG.Proof.X25519.AArch64.hi, loPairs, hiPairs, List.map_map, List.map_map]
    simp only [BitVec.toNat_setWidth, Function.comp_def, VG.Proof.X25519.AArch64.sum_range_list,
      show (19 : BitVec 64).toNat = 19 from rfl]
    have hl : ∀ i < k + 1, VG.Proof.X25519.AArch64.wd s.mem b (a + 8 * i) * VG.Proof.X25519.AArch64.wd s.mem b (c + 8 * (k - i)) =
        VG.Proof.X25519.AArch64.limbs s.mem b a i * VG.Proof.X25519.AArch64.limbs s.mem b c (k - i) := fun i hi => by
      simp only [VG.Proof.X25519.AArch64.limbs, show i < 15 by omega, show k - i < 15 by omega, ite_true]
    have hh : ∀ j < 14 - k, VG.Proof.X25519.AArch64.wd s.mem b (a + 8 * (k + 1 + j)) * VG.Proof.X25519.AArch64.wd s.mem b (c + 8 * (14 - j)) =
        VG.Proof.X25519.AArch64.limbs s.mem b a (k + 1 + j) * VG.Proof.X25519.AArch64.limbs s.mem b c (14 - j) := fun j hj => by
      simp only [VG.Proof.X25519.AArch64.limbs, show k + 1 + j < 15 by omega, show 14 - j < 15 by omega, ite_true]
    rw [VG.Proof.X25519.AArch64.sumR_congr hl, VG.Proof.X25519.AArch64.sumR_congr hh, show (0 : BitVec 16).toNat = 0 from rfl,
      Nat.zero_mod, Nat.zero_add, Nat.zero_add]
  · exact (((VG.Proof.X25519.AArch64.kp_wx s _ _).trans k₁).trans (((VG.Proof.X25519.AArch64.kp_wx s₁ _ _).trans k₃).trans (VG.Proof.X25519.AArch64.kp_wx s₃ _ _))).sub
      (by sub_regs)
  · rw [VG.Proof.X25519.AArch64.mem_wx, m₃, VG.Proof.X25519.AArch64.mem_wx, m₁, VG.Proof.X25519.AArch64.mem_wx]

/-- The limb registers, as a function (zero beyond the fifteenth). -/
def regs (s : State) (k : Nat) : Nat := if k < 15 then VG.Proof.X25519.AArch64.v s (dreg k) else 0

/-- The registers the columns write. -/
abbrev colRegs : List Reg := DR ++ [.x17, .x19, .x20]

theorem dreg_sub {k : Nat} (hk : k < 15) : [Reg.x17, .x19, .x20, dreg k] ⊆ VG.Proof.X25519.AArch64.colRegs := by
  have := VG.Proof.X25519.AArch64.dreg_mem k hk
  simp only [List.cons_subset, List.nil_subset, and_true, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, true_or, or_true, this]

/-- The first `n` columns. -/
theorem cols_ok {b : Addr} {a c : Nat} (ha : VG.Proof.X25519.AArch64.Slot a) (hc : VG.Proof.X25519.AArch64.Slot c) :
    ∀ n ≤ 15, ∀ s : State, VG.Proof.X25519.AArch64.Sc b s → s.gpr .x21 = 19 →
    WP isa (.block ((List.range n).flatMap (col a c))) s fun s' =>
      (∀ k < n, VG.Proof.X25519.AArch64.v s' (dreg k) = VG.Proof.X25519.AArch64.colM (VG.Proof.X25519.AArch64.limbs s.mem b a) (VG.Proof.X25519.AArch64.limbs s.mem b c) k) ∧ VG.Proof.X25519.AArch64.Kp VG.Proof.X25519.AArch64.colRegs s s' ∧
        s'.mem = s.mem
  | 0, _, s, _, _ => WP.block_nil ⟨fun k hk => absurd hk (Nat.not_lt_zero _), Kp.refl _ _, rfl⟩
  | n + 1, hn, s, hs, h19 => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.cols_ok ha hc n (by omega) s hs h19) fun s₁ ⟨e₁, k₁, m₁⟩ => ?_)
    have hs₁ := hs.of_kp k₁ (by decide)
    have h19₁ : s₁.gpr .x21 = 19 := by rw [k₁.gpr _ (by decide), h19]
    refine WP.mono (VG.Proof.X25519.AArch64.col_ok hs₁ h19₁ ha hc (k := n) (by omega)) fun s₂ ⟨e₂, k₂, m₂⟩ =>
      ⟨fun k hk => ?_, (k₁.trans (k₂.sub (VG.Proof.X25519.AArch64.dreg_sub (by omega)))).sub
        (List.append_subset.mpr ⟨List.Subset.refl _, List.Subset.refl _⟩), m₂.trans m₁⟩
    · rw [m₁] at e₂
      by_cases hkn : k = n
      · rw [hkn, e₂]
      · obtain ⟨d17, d19, d20, -⟩ := VG.Proof.X25519.AArch64.dreg_facts k (by omega)
        have hne : dreg k ≠ dreg n := fun h => hkn (VG.Proof.X25519.AArch64.dreg_inj k (by omega) n (by omega) h)
        have hnot : dreg k ∉ [Reg.x17, .x19, .x20, dreg n] := by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨d17, d19, d20, hne⟩
        rw [VG.Proof.X25519.AArch64.v, k₂.gpr _ hnot]
        exact e₁ k (by omega)

/-! ## Carries -/

theorem dreg_ne {j k : Nat} (hj : j < 15) (hk : k < 15) (h : j ≠ k) : dreg j ≠ dreg k :=
  fun e => h (VG.Proof.X25519.AArch64.dreg_inj j hj k hk e)

/-- The carry out of limb `k` into limb `k'`. -/
theorem carryStep_ok {s : State} {k k' : Nat} (hk : k < 15) (hk' : k' < 15) (hkk : k ≠ k')
    (hm : s.gpr .x22 = 0x1ffff) :
    WP isa (.block (carryStep k k')) s fun s' =>
      VG.Proof.X25519.AArch64.regs s' = VG.Proof.X25519.AArch64.cstep k k' (VG.Proof.X25519.AArch64.regs s) ∧ VG.Proof.X25519.AArch64.Kp VG.Proof.X25519.AArch64.colRegs s s' ∧ s'.mem = s.mem := by
  obtain ⟨d17, -, -, -, d22, -⟩ := VG.Proof.X25519.AArch64.dreg_facts k hk
  obtain ⟨d17', -⟩ := VG.Proof.X25519.AArch64.dreg_facts k' hk'
  have hne := VG.Proof.X25519.AArch64.dreg_ne hk hk' hkk
  apply WP.of_runBlock
  simp only [carryStep, runBlock_cons, VG.Proof.X25519.AArch64.exec_lsr (show 17 < 64 by decide), runStep_some, VG.Proof.X25519.AArch64.exec_and_x,
    VG.Proof.X25519.AArch64.exec_add_x, runBlock_nil, Option.some.injEq, exists_eq_left']
  refine ⟨funext fun i => ?_, ?_, rfl⟩
  · simp only [VG.Proof.X25519.AArch64.regs, VG.Proof.X25519.AArch64.cstep]
    by_cases hi : i < 15
    · simp only [hi, ite_true, show k < 15 from hk, show k' < 15 from hk']
      by_cases hik : i = k
      · subst hik
        rw [ite_eq_left rfl, VG.Proof.X25519.AArch64.v, VG.Proof.X25519.AArch64.gpr_wx_ne _ _ hne, VG.Proof.X25519.AArch64.gpr_wx_self, VG.Proof.X25519.AArch64.gpr_wx_ne _ _ d17, VG.Proof.X25519.AArch64.gpr_wx_ne _ _ (by decide),
          VG.Proof.X25519.AArch64.and_mask17 _ _ hm]
      · rw [ite_eq_right hik]
        by_cases hik' : i = k'
        · subst hik'
          rw [ite_eq_left rfl, VG.Proof.X25519.AArch64.v, VG.Proof.X25519.AArch64.gpr_wx_self, VG.Proof.X25519.AArch64.gpr_wx_ne _ _ (Ne.symm hne), VG.Proof.X25519.AArch64.gpr_wx_ne _ _ d17',
            VG.Proof.X25519.AArch64.gpr_wx_ne _ _ (Ne.symm d17), VG.Proof.X25519.AArch64.gpr_wx_self, BitVec.toNat_add, VG.Proof.X25519.AArch64.lsr_toNat]
        · rw [ite_eq_right hik']
          have h1 := VG.Proof.X25519.AArch64.dreg_ne hi hk hik
          have h2 := VG.Proof.X25519.AArch64.dreg_ne hi hk' hik'
          obtain ⟨e17, -⟩ := VG.Proof.X25519.AArch64.dreg_facts i hi
          rw [VG.Proof.X25519.AArch64.v, VG.Proof.X25519.AArch64.v, VG.Proof.X25519.AArch64.gpr_wx_ne _ _ h2, VG.Proof.X25519.AArch64.gpr_wx_ne _ _ h1, VG.Proof.X25519.AArch64.gpr_wx_ne _ _ e17]
    · simp only [hi, ite_false, show i ≠ k by omega, show i ≠ k' by omega]
  · exact (((VG.Proof.X25519.AArch64.kp_wx s _ _).trans (VG.Proof.X25519.AArch64.kp_wx _ _ _)).trans (VG.Proof.X25519.AArch64.kp_wx _ _ _)).sub (by
      have := VG.Proof.X25519.AArch64.dreg_mem k hk
      have := VG.Proof.X25519.AArch64.dreg_mem k' hk'
      simp only [List.cons_subset, List.nil_subset, and_true, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false, true_or, or_true, *, List.cons_append, List.nil_append])

/-- The carry out of limb 14 into limb 0. -/
theorem foldTop_ok {s : State} (hm : s.gpr .x22 = 0x1ffff) (h19 : s.gpr .x21 = 19) :
    WP isa (.block foldTop) s fun s' =>
      VG.Proof.X25519.AArch64.regs s' = VG.Proof.X25519.AArch64.cfold (VG.Proof.X25519.AArch64.regs s) ∧ VG.Proof.X25519.AArch64.Kp VG.Proof.X25519.AArch64.colRegs s s' ∧ s'.mem = s.mem := by
  obtain ⟨d17, -, -, d21, d22, -⟩ := VG.Proof.X25519.AArch64.dreg_facts 14 (by decide)
  obtain ⟨e17, -, -, e21, e22, -⟩ := VG.Proof.X25519.AArch64.dreg_facts 0 (by decide)
  have hne := VG.Proof.X25519.AArch64.dreg_ne (j := 0) (k := 14) (by decide) (by decide) (by decide)
  apply WP.of_runBlock
  simp only [foldTop, runBlock_cons, VG.Proof.X25519.AArch64.exec_lsr (show 17 < 64 by decide), runStep_some, VG.Proof.X25519.AArch64.exec_and_x,
    VG.Proof.X25519.AArch64.exec_madd_x, runBlock_nil, Option.some.injEq, exists_eq_left']
  refine ⟨funext fun i => ?_, ?_, rfl⟩
  · simp only [VG.Proof.X25519.AArch64.regs, VG.Proof.X25519.AArch64.cfold]
    by_cases hi : i < 15
    · simp only [hi, ite_true, show (14 : Nat) < 15 by decide, show (0 : Nat) < 15 by decide]
      by_cases hi14 : i = 14
      · subst hi14
        rw [ite_eq_left rfl, VG.Proof.X25519.AArch64.v, VG.Proof.X25519.AArch64.gpr_wx_ne _ _ (Ne.symm hne), VG.Proof.X25519.AArch64.gpr_wx_self, VG.Proof.X25519.AArch64.gpr_wx_ne _ _ d17,
          VG.Proof.X25519.AArch64.gpr_wx_ne _ _ (by decide), VG.Proof.X25519.AArch64.and_mask17 _ _ hm]
      · rw [ite_eq_right hi14]
        by_cases hi0 : i = 0
        · subst hi0
          rw [ite_eq_left rfl, VG.Proof.X25519.AArch64.v, VG.Proof.X25519.AArch64.gpr_wx_self, VG.Proof.X25519.AArch64.gpr_wx_ne _ _ hne, VG.Proof.X25519.AArch64.gpr_wx_ne _ _ e17,
            VG.Proof.X25519.AArch64.gpr_wx_ne _ _ (Ne.symm d17), VG.Proof.X25519.AArch64.gpr_wx_self, VG.Proof.X25519.AArch64.gpr_wx_ne _ _ (Ne.symm d21), VG.Proof.X25519.AArch64.gpr_wx_ne _ _ (by decide),
            h19, VG.Proof.X25519.AArch64.madd_toNat, VG.Proof.X25519.AArch64.lsr_toNat]
          rfl
        · rw [ite_eq_right hi0]
          have h1 := VG.Proof.X25519.AArch64.dreg_ne hi (by decide : (14 : Nat) < 15) hi14
          have h2 := VG.Proof.X25519.AArch64.dreg_ne hi (by decide : (0 : Nat) < 15) hi0
          obtain ⟨f17, -⟩ := VG.Proof.X25519.AArch64.dreg_facts i hi
          rw [VG.Proof.X25519.AArch64.v, VG.Proof.X25519.AArch64.v, VG.Proof.X25519.AArch64.gpr_wx_ne _ _ h2, VG.Proof.X25519.AArch64.gpr_wx_ne _ _ h1, VG.Proof.X25519.AArch64.gpr_wx_ne _ _ f17]
    · simp only [hi, ite_false, show i ≠ 14 by omega, show i ≠ 0 by omega]
  · exact (((VG.Proof.X25519.AArch64.kp_wx s _ _).trans (VG.Proof.X25519.AArch64.kp_wx _ _ _)).trans (VG.Proof.X25519.AArch64.kp_wx _ _ _)).sub (by
      simp only [List.cons_subset, List.nil_subset, and_true, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false, true_or, or_true, List.cons_append, List.nil_append,
        VG.Proof.X25519.AArch64.dreg_mem 14 (by decide), VG.Proof.X25519.AArch64.dreg_mem 0 (by decide)])

/-- The carries from limb 0 to limb `n`. -/
theorem chain_ok : ∀ n ≤ 14, ∀ s : State, s.gpr .x22 = 0x1ffff →
    WP isa (.block ((List.range n).flatMap fun k => carryStep k (k + 1))) s fun s' =>
      VG.Proof.X25519.AArch64.regs s' = VG.Proof.X25519.AArch64.chainN (VG.Proof.X25519.AArch64.regs s) n ∧ VG.Proof.X25519.AArch64.Kp VG.Proof.X25519.AArch64.colRegs s s' ∧ s'.mem = s.mem
  | 0, _, s, _ => WP.block_nil ⟨rfl, Kp.refl _ _, rfl⟩
  | n + 1, hn, s, hm => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.chain_ok n (by omega) s hm) fun s₁ ⟨e₁, k₁, m₁⟩ => ?_)
    have hm₁ : s₁.gpr .x22 = 0x1ffff := by rw [k₁.gpr _ (by decide), hm]
    refine WP.mono (VG.Proof.X25519.AArch64.carryStep_ok (k := n) (k' := n + 1) (by omega) (by omega) (by omega) hm₁)
      fun s₂ ⟨e₂, k₂, m₂⟩ => ⟨?_, (k₁.trans k₂).sub
        (List.append_subset.mpr ⟨List.Subset.refl _, List.Subset.refl _⟩), m₂.trans m₁⟩
    rw [e₂, e₁]; rfl

theorem mask17_ok (s : State) :
    WP isa (.block mask17) s fun s' => s'.gpr .x22 = 0x1ffff ∧ VG.Proof.X25519.AArch64.Kp [.x22] s s' ∧ s'.mem = s.mem := by
  apply WP.of_runBlock
  simp only [mask17, runBlock_cons, VG.Proof.X25519.AArch64.exec_movz, runStep_some, VG.Proof.X25519.AArch64.exec_movk1, runBlock_nil,
    Option.some.injEq, exists_eq_left', VG.Proof.X25519.AArch64.gpr_wx_self]
  exact ⟨by decide, ((VG.Proof.X25519.AArch64.kp_wx s _ _).trans (VG.Proof.X25519.AArch64.kp_wx _ _ _)).sub (by sub_regs), rfl⟩

theorem const19_ok (s : State) :
    WP isa (.block const19) s fun s' => s'.gpr .x21 = 19 ∧ VG.Proof.X25519.AArch64.Kp [.x21] s s' ∧ s'.mem = s.mem := by
  apply WP.of_runBlock
  simp only [const19, runBlock_cons, VG.Proof.X25519.AArch64.exec_movz, runStep_some, runBlock_nil,
    Option.some.injEq, exists_eq_left', VG.Proof.X25519.AArch64.gpr_wx_self]
  exact ⟨by decide, VG.Proof.X25519.AArch64.kp_wx s _ _, rfl⟩

/-- The registers of the field operations. -/
abbrev fieldRegs : List Reg := VG.Proof.X25519.AArch64.colRegs ++ [.x21, .x22]

theorem sub_field {W : List Reg} (h : ∀ r ∈ W, r ∈ VG.Proof.X25519.AArch64.fieldRegs) : W ⊆ VG.Proof.X25519.AArch64.fieldRegs := fun _ hr => h _ hr

/-- All the carries of a product. -/
theorem carry_ok {s : State} (h19 : s.gpr .x21 = 19) :
    WP isa (.block carry) s fun s' =>
      VG.Proof.X25519.AArch64.regs s' = VG.Proof.X25519.AArch64.carryF (VG.Proof.X25519.AArch64.regs s) ∧ VG.Proof.X25519.AArch64.Kp VG.Proof.X25519.AArch64.fieldRegs s s' ∧ s'.mem = s.mem := by
  rw [carry, List.append_assoc, List.append_assoc, List.append_assoc]
  refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.mask17_ok s) fun s₁ ⟨e₁, k₁, m₁⟩ => ?_)
  have r₁ : VG.Proof.X25519.AArch64.regs s₁ = VG.Proof.X25519.AArch64.regs s := funext fun i => by
    simp only [VG.Proof.X25519.AArch64.regs]
    split
    · rename_i hi
      rw [VG.Proof.X25519.AArch64.v, k₁.gpr _ (by simpa using (VG.Proof.X25519.AArch64.dreg_facts i hi).2.2.2.2.1)]
    · rfl
  have h19₁ : s₁.gpr .x21 = 19 := by rw [k₁.gpr _ (by decide), h19]
  refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.chain_ok 14 (by decide) s₁ e₁) fun s₂ ⟨e₂, k₂, m₂⟩ => ?_)
  have hm₂ : s₂.gpr .x22 = 0x1ffff := by rw [k₂.gpr _ (by decide), e₁]
  have h19₂ : s₂.gpr .x21 = 19 := by rw [k₂.gpr _ (by decide), h19₁]
  refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.foldTop_ok hm₂ h19₂) fun s₃ ⟨e₃, k₃, m₃⟩ => ?_)
  have hm₃ : s₃.gpr .x22 = 0x1ffff := by rw [k₃.gpr _ (by decide), hm₂]
  refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.carryStep_ok (k := 0) (k' := 1) (by decide) (by decide) (by decide) hm₃)
    fun s₄ ⟨e₄, k₄, m₄⟩ => ?_)
  have hm₄ : s₄.gpr .x22 = 0x1ffff := by rw [k₄.gpr _ (by decide), hm₃]
  refine WP.mono (VG.Proof.X25519.AArch64.carryStep_ok (k := 1) (k' := 2) (by decide) (by decide) (by decide) hm₄)
    fun s₅ ⟨e₅, k₅, m₅⟩ => ⟨?_, ?_, by rw [m₅, m₄, m₃, m₂, m₁]⟩
  · rw [e₅, e₄, e₃, e₂, r₁]; rfl
  · refine (k₁.trans (k₂.trans (k₃.trans (k₄.trans k₅)))).sub fun r hr => ?_
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with hr | hr | hr | hr | hr
    · exact Or.inr (Or.inr hr)
    all_goals exact Or.inl hr

/-! ## Stores -/

theorem wd_writeW (m : Mem) (b : Addr) {o off : Nat} (x : BitVec 64) (ho : VG.Proof.X25519.AArch64.Off o) (hoff : VG.Proof.X25519.AArch64.Off off) :
    VG.Proof.X25519.AArch64.wd (m.writeW (b + BitVec.ofNat 64 o) x) b off = if off = o then x.toNat else VG.Proof.X25519.AArch64.wd m b off := by
  have := ho.2; have := hoff.2
  by_cases h : off = o
  · subst h; rw [ite_eq_left rfl, VG.Proof.X25519.AArch64.wd, Mem.readW_writeW_self64]
  · rw [ite_eq_right h, VG.Proof.X25519.AArch64.wd, VG.Proof.X25519.AArch64.wd, Mem.readW_writeW_sep (Offset.sep b (by have := ho.1; have := hoff.1; omega)
      (by omega) (by omega)) (by decide)]

/-- The region of the element at `o`. -/
abbrev slotR (b : Addr) (o : Nat) : Region := ⟨b + BitVec.ofNat 64 o, 120⟩

theorem slot_contains (b : Addr) {o k : Nat} (ho : VG.Proof.X25519.AArch64.Slot o) (hk : k < 15) :
    (VG.Proof.X25519.AArch64.slotR b o).Contains (b + BitVec.ofNat 64 (o + 8 * k)) (64 / 8) :=
  Offset.contains b (by omega) (by omega) (by have := ho.2; omega)

theorem stores_ok {b : Addr} {o : Nat} (ho : VG.Proof.X25519.AArch64.Slot o) :
    ∀ n ≤ 15, ∀ s : State, VG.Proof.X25519.AArch64.Sc b s →
    WP isa (.block ((List.range n).map fun k => st (dreg k) (o + 8 * k))) s fun s' =>
      (∀ k < n, VG.Proof.X25519.AArch64.wd s'.mem b (o + 8 * k) = VG.Proof.X25519.AArch64.v s (dreg k)) ∧ Frame [VG.Proof.X25519.AArch64.slotR b o] s.mem s'.mem ∧
        VG.Proof.X25519.AArch64.Kp [] s s'
  | 0, _, s, _ => WP.block_nil ⟨fun k hk => absurd hk (Nat.not_lt_zero _), Frame.refl _ _, Kp.refl _ _⟩
  | n + 1, hn, s, hs => by
    rw [List.range_succ, List.map_append, List.map_singleton]
    refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.stores_ok ho n (by omega) s hs) fun s₁ ⟨e₁, f₁, k₁⟩ => ?_)
    have hs₁ := hs.of_kp k₁ (by decide)
    refine WP.block_cons_iff.mpr ⟨_, VG.Proof.X25519.AArch64.exec_st hs₁ _ (ho.off (by omega)), WP.block_nil ⟨fun k hk => ?_, ?_, ?_⟩⟩
    · simp only
      rw [VG.Proof.X25519.AArch64.wd_writeW _ _ _ (ho.off (by omega)) (ho.off (by omega))]
      by_cases hkn : k = n
      · subst hkn; rw [ite_eq_left rfl, k₁.gpr _ (by simp)]
      · rw [ite_eq_right (by omega)]; exact e₁ k (by omega)
    · exact f₁.writeW (List.mem_singleton_self _) _ (VG.Proof.X25519.AArch64.slot_contains b ho (by omega))
    · exact ⟨fun r _ => k₁.gpr r (by simp), k₁.rd, k₁.wr⟩

/-- The limbs stored at `o`. -/
theorem store_ok {b : Addr} {s : State} (hs : VG.Proof.X25519.AArch64.Sc b s) {o : Nat} (ho : VG.Proof.X25519.AArch64.Slot o) :
    WP isa (.block (store o)) s fun s' =>
      VG.Proof.X25519.AArch64.limbs s'.mem b o = VG.Proof.X25519.AArch64.regs s ∧ Frame [VG.Proof.X25519.AArch64.slotR b o] s.mem s'.mem ∧ VG.Proof.X25519.AArch64.Kp [] s s' :=
  WP.mono (VG.Proof.X25519.AArch64.stores_ok ho 15 (by decide) s hs) fun s' ⟨e, f, k⟩ => ⟨funext fun i => by
    simp only [VG.Proof.X25519.AArch64.limbs, VG.Proof.X25519.AArch64.regs]
    split
    · rename_i hi; exact e i hi
    · rfl, f, k⟩

/-! ## Multiplication -/

theorem regs_cols {b : Addr} {s s' : State} {a c : Nat}
    (h : ∀ k < 15, VG.Proof.X25519.AArch64.v s' (dreg k) = VG.Proof.X25519.AArch64.colM (VG.Proof.X25519.AArch64.limbs s.mem b a) (VG.Proof.X25519.AArch64.limbs s.mem b c) k) :
    VG.Proof.X25519.AArch64.regs s' = VG.Proof.X25519.AArch64.cols (VG.Proof.X25519.AArch64.limbs s.mem b a) (VG.Proof.X25519.AArch64.limbs s.mem b c) := funext fun k => by
  simp only [VG.Proof.X25519.AArch64.regs, VG.Proof.X25519.AArch64.cols]; split
  · rename_i hk; exact h k hk
  · rfl

/-- `[o] = [a] · [c]`. -/
theorem mul_ok {b : Addr} {s : State} (hs : VG.Proof.X25519.AArch64.Sc b s) {o a c : Nat} (ho : VG.Proof.X25519.AArch64.Slot o) (ha : VG.Proof.X25519.AArch64.Slot a)
    (hc : VG.Proof.X25519.AArch64.Slot c) :
    WP isa (.block (mul o a c)) s fun s' =>
      VG.Proof.X25519.AArch64.limbs s'.mem b o = VG.Proof.X25519.AArch64.mulF (VG.Proof.X25519.AArch64.limbs s.mem b a) (VG.Proof.X25519.AArch64.limbs s.mem b c) ∧ Frame [VG.Proof.X25519.AArch64.slotR b o] s.mem s'.mem ∧
        VG.Proof.X25519.AArch64.Kp VG.Proof.X25519.AArch64.fieldRegs s s' := by
  rw [mul, List.append_assoc, List.append_assoc]
  refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.const19_ok s) fun s₁ ⟨e₁, k₁, m₁⟩ => ?_)
  have hs₁ := hs.of_kp k₁ (by decide)
  refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.cols_ok ha hc 15 (by decide) s₁ hs₁ e₁) fun s₂ ⟨e₂, k₂, m₂⟩ => ?_)
  have hs₂ := hs₁.of_kp k₂ (by decide)
  have h19₂ : s₂.gpr .x21 = 19 := by rw [k₂.gpr _ (by decide), e₁]
  refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.carry_ok h19₂) fun s₃ ⟨e₃, k₃, m₃⟩ => ?_)
  have hs₃ := hs₂.of_kp k₃ (by decide)
  refine WP.mono (VG.Proof.X25519.AArch64.store_ok hs₃ ho) fun s₄ ⟨e₄, f₄, k₄⟩ => ⟨?_, ?_, ?_⟩
  · rw [e₄, e₃, VG.Proof.X25519.AArch64.regs_cols e₂, m₁]; rfl
  · rw [← m₁, ← m₂, ← m₃]; exact f₄
  · exact (k₁.trans (k₂.trans (k₃.trans k₄))).sub (List.append_subset.mpr ⟨by decide,
      List.append_subset.mpr ⟨List.subset_append_left _ _, by simp⟩⟩)

end VG.Proof.X25519.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.AArch64.Limbwise`. -/
section

/-!
# X25519 on AArch64: the operations limb by limb

`add`, `sub`, `copy`, `cswap` and `mulSmall`: the first four compute each limb
of their result from the same limb of their operands, loading them before
storing it, so their result may be one of their operands.
-/

namespace VG.Proof.X25519.AArch64

open VG VG.AArch64 VG.Impl.X25519.AArch64

/-- The offsets `off` and `o` are of the same element, or of disjoint ones. -/
def Alias (o off : Nat) : Prop := o = off ∨ o + 120 ≤ off ∨ off + 120 ≤ o

instance (o off : Nat) : Decidable (VG.Proof.X25519.AArch64.Alias o off) := by unfold VG.Proof.X25519.AArch64.Alias; infer_instance

theorem Alias.ne {o a : Nat} (h : VG.Proof.X25519.AArch64.Alias o a) {i j : Nat} (hi : i < 15) (hj : j < i) :
    a + 8 * i ≠ o + 8 * j := by
  rcases h with rfl | h | h <;> omega

/-- A block that computes each limb of the element at `o` from words it reads
(`reads i`, none a limb of `o` already written), and stores it. -/
theorem limbwise_ok {b : Addr} {o : Nat} (ho : VG.Proof.X25519.AArch64.Slot o) (body : Nat → List Instr) (W : List Reg)
    (hW : Reg.x3 ∉ W) (val : Nat → Mem → Nat) (reads : Nat → List Nat) (I : State → Prop)
    (hI : ∀ s s', I s → VG.Proof.X25519.AArch64.Kp W s s' → I s')
    (hstep : ∀ i < 15, ∀ s : State, VG.Proof.X25519.AArch64.Sc b s → I s → WP isa (.block (body i)) s fun s' =>
      ∃ x : BitVec 64, x.toNat = val i s.mem ∧ s'.mem = s.mem.writeW (b + BitVec.ofNat 64 (o + 8 * i)) x ∧
        VG.Proof.X25519.AArch64.Kp W s s')
    (hval : ∀ i < 15, ∀ m m' : Mem, (∀ off ∈ reads i, VG.Proof.X25519.AArch64.wd m' b off = VG.Proof.X25519.AArch64.wd m b off) → val i m' = val i m)
    (hreads : ∀ i < 15, ∀ off ∈ reads i, VG.Proof.X25519.AArch64.Off off ∧ ∀ j < i, off ≠ o + 8 * j) :
    ∀ n ≤ 15, ∀ s : State, VG.Proof.X25519.AArch64.Sc b s → I s → WP isa (.block ((List.range n).flatMap body)) s fun s' =>
      (∀ k < n, VG.Proof.X25519.AArch64.wd s'.mem b (o + 8 * k) = val k s.mem) ∧
      (∀ off, VG.Proof.X25519.AArch64.Off off → (∀ j < n, off ≠ o + 8 * j) → VG.Proof.X25519.AArch64.wd s'.mem b off = VG.Proof.X25519.AArch64.wd s.mem b off) ∧
      Frame [VG.Proof.X25519.AArch64.slotR b o] s.mem s'.mem ∧ VG.Proof.X25519.AArch64.Kp W s s'
  | 0, _, s, _, _ => WP.block_nil ⟨fun k hk => absurd hk (Nat.not_lt_zero _), fun _ _ _ => rfl,
      Frame.refl _ _, Kp.refl _ _⟩
  | n + 1, hn, s, hs, hIs => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.limbwise_ok ho body W hW val reads I hI hstep hval hreads n (by omega)
      s hs hIs) fun s₁ ⟨e₁, u₁, f₁, k₁⟩ => ?_)
    refine WP.mono (hstep n (by omega) s₁ (hs.of_kp k₁ hW) (hI _ _ hIs k₁)) fun s₂ ⟨x, hx, m₂, k₂⟩ => ⟨fun k hk => ?_,
      fun off hoff hj => ?_, ?_, (k₁.trans k₂).sub (List.append_subset.mpr ⟨List.Subset.refl _,
        List.Subset.refl _⟩)⟩
    · rw [m₂, VG.Proof.X25519.AArch64.wd_writeW _ _ _ (ho.off (by omega)) (ho.off (by omega))]
      by_cases hkn : k = n
      · subst hkn
        rw [ite_eq_left rfl, hx]
        exact hval k (by omega) _ _ fun off hoff =>
          u₁ off (hreads k (by omega) off hoff).1 (hreads k (by omega) off hoff).2
      · rw [ite_eq_right (by omega)]; exact e₁ k (by omega)
    · rw [m₂, VG.Proof.X25519.AArch64.wd_writeW _ _ _ (ho.off (by omega)) hoff, ite_eq_right (hj n (by omega))]
      exact u₁ off hoff fun j hjn => hj j (by omega)
    · rw [m₂]; exact f₁.writeW (List.mem_singleton_self _) _ (VG.Proof.X25519.AArch64.slot_contains b ho (by omega))

/-- The whole element. -/
theorem limbwise_all {b : Addr} {o : Nat} (ho : VG.Proof.X25519.AArch64.Slot o) (body : Nat → List Instr) (W : List Reg)
    (hW : Reg.x3 ∉ W) (val : Nat → Mem → Nat) (reads : Nat → List Nat) (I : State → Prop)
    (hI : ∀ s s', I s → VG.Proof.X25519.AArch64.Kp W s s' → I s')
    (hstep : ∀ i < 15, ∀ s : State, VG.Proof.X25519.AArch64.Sc b s → I s → WP isa (.block (body i)) s fun s' =>
      ∃ x : BitVec 64, x.toNat = val i s.mem ∧ s'.mem = s.mem.writeW (b + BitVec.ofNat 64 (o + 8 * i)) x ∧
        VG.Proof.X25519.AArch64.Kp W s s')
    (hval : ∀ i < 15, ∀ m m' : Mem, (∀ off ∈ reads i, VG.Proof.X25519.AArch64.wd m' b off = VG.Proof.X25519.AArch64.wd m b off) → val i m' = val i m)
    (hreads : ∀ i < 15, ∀ off ∈ reads i, VG.Proof.X25519.AArch64.Off off ∧ ∀ j < i, off ≠ o + 8 * j) {s : State} (hs : VG.Proof.X25519.AArch64.Sc b s)
    (hIs : I s) :
    WP isa (.block ((List.range 15).flatMap body)) s fun s' =>
      VG.Proof.X25519.AArch64.limbs s'.mem b o = (fun k => if k < 15 then val k s.mem else 0) ∧
      Frame [VG.Proof.X25519.AArch64.slotR b o] s.mem s'.mem ∧ VG.Proof.X25519.AArch64.Kp W s s' :=
  WP.mono (VG.Proof.X25519.AArch64.limbwise_ok ho body W hW val reads I hI hstep hval hreads 15 (by decide) s hs hIs)
    fun _ ⟨e, _, f, k⟩ => ⟨funext fun i => by
      simp only [VG.Proof.X25519.AArch64.limbs]; split
      · rename_i hi; exact e i hi
      · rfl, f, k⟩

/-! ## Sums -/

/-- One limb of `add`. -/
theorem addStep_ok {b : Addr} {s : State} (hs : VG.Proof.X25519.AArch64.Sc b s) {o a c i : Nat} (ho : VG.Proof.X25519.AArch64.Off (o + 8 * i))
    (ha : VG.Proof.X25519.AArch64.Off (a + 8 * i)) (hc : VG.Proof.X25519.AArch64.Off (c + 8 * i)) :
    WP isa (.block [ld .x17 (a + 8 * i), ld .x19 (c + 8 * i), .add .x .x17 .x17 .x19, st .x17 (o + 8 * i)]) s
      fun s' => ∃ x : BitVec 64, x.toNat = (VG.Proof.X25519.AArch64.wd s.mem b (a + 8 * i) + VG.Proof.X25519.AArch64.wd s.mem b (c + 8 * i)) % 2 ^ 64 ∧
        s'.mem = s.mem.writeW (b + BitVec.ofNat 64 (o + 8 * i)) x ∧ VG.Proof.X25519.AArch64.Kp [.x17, .x19] s s' := by
  have hs1 := VG.Proof.X25519.AArch64.sc_wx s (s.mem.readW (b + BitVec.ofNat 64 (a + 8 * i)) 64) hs (show Reg.x17 ≠ .x3 by decide)
  have hs2 := VG.Proof.X25519.AArch64.sc_wx _ (s.mem.readW (b + BitVec.ofNat 64 (c + 8 * i)) 64) hs1 (show Reg.x19 ≠ .x3 by decide)
  have hs3 := VG.Proof.X25519.AArch64.sc_wx _ (s.mem.readW (b + BitVec.ofNat 64 (a + 8 * i)) 64 + s.mem.readW (b + BitVec.ofNat 64 (c + 8 * i)) 64)
    hs2 (show Reg.x17 ≠ .x3 by decide)
  apply WP.of_runBlock
  simp only [runBlock_cons, VG.Proof.X25519.AArch64.exec_ld hs _ ha, runStep_some, VG.Proof.X25519.AArch64.exec_ld hs1 _ hc, VG.Proof.X25519.AArch64.mem_wx, VG.Proof.X25519.AArch64.exec_add_x,
    VG.Proof.X25519.AArch64.gpr_wx_self, VG.Proof.X25519.AArch64.gpr_wx_ne _ _ (show Reg.x17 ≠ .x19 by decide)]
  rw [VG.Proof.X25519.AArch64.exec_st hs3 _ ho]
  simp only [runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left', VG.Proof.X25519.AArch64.mem_wx, VG.Proof.X25519.AArch64.gpr_wx_self]
  refine ⟨_, ?_, rfl, ⟨fun r hr => ?_, rfl, rfl⟩⟩
  · rw [BitVec.toNat_add, VG.Proof.X25519.AArch64.wd_def, VG.Proof.X25519.AArch64.wd_def]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    show (State.write _ _ _ _).gpr r = _
    rw [VG.Proof.X25519.AArch64.gpr_wx_ne _ _ hr.1, VG.Proof.X25519.AArch64.gpr_wx_ne _ _ hr.2, VG.Proof.X25519.AArch64.gpr_wx_ne _ _ hr.1]

theorem val_congr2 {b : Addr} {m m' : Mem} {p q : Nat} (h : ∀ off ∈ [p, q], VG.Proof.X25519.AArch64.wd m' b off = VG.Proof.X25519.AArch64.wd m b off) :
    VG.Proof.X25519.AArch64.wd m' b p = VG.Proof.X25519.AArch64.wd m b p ∧ VG.Proof.X25519.AArch64.wd m' b q = VG.Proof.X25519.AArch64.wd m b q :=
  ⟨h p (by simp), h q (by simp)⟩

theorem reads2 {o a c : Nat} (ha : VG.Proof.X25519.AArch64.Slot a) (hc : VG.Proof.X25519.AArch64.Slot c) (hoa : VG.Proof.X25519.AArch64.Alias o a) (hoc : VG.Proof.X25519.AArch64.Alias o c) :
    ∀ i < 15, ∀ off ∈ [a + 8 * i, c + 8 * i], VG.Proof.X25519.AArch64.Off off ∧ ∀ j < i, off ≠ o + 8 * j := by
  intro i hi off hoff
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
  rcases hoff with rfl | rfl
  · exact ⟨ha.off hi, fun j hj => hoa.ne hi hj⟩
  · exact ⟨hc.off hi, fun j hj => hoc.ne hi hj⟩

/-- `[o] = [a] + [c]`. -/
theorem add_ok {b : Addr} {s : State} (hs : VG.Proof.X25519.AArch64.Sc b s) {o a c : Nat} (ho : VG.Proof.X25519.AArch64.Slot o) (ha : VG.Proof.X25519.AArch64.Slot a)
    (hc : VG.Proof.X25519.AArch64.Slot c) (hoa : VG.Proof.X25519.AArch64.Alias o a) (hoc : VG.Proof.X25519.AArch64.Alias o c) :
    WP isa (.block (add o a c)) s fun s' =>
      VG.Proof.X25519.AArch64.limbs s'.mem b o = VG.Proof.X25519.AArch64.addF (VG.Proof.X25519.AArch64.limbs s.mem b a) (VG.Proof.X25519.AArch64.limbs s.mem b c) ∧ Frame [VG.Proof.X25519.AArch64.slotR b o] s.mem s'.mem ∧
        VG.Proof.X25519.AArch64.Kp [.x17, .x19] s s' := by
  refine WP.mono (VG.Proof.X25519.AArch64.limbwise_all ho _ [.x17, .x19] (by decide)
    (fun i m => (VG.Proof.X25519.AArch64.wd m b (a + 8 * i) + VG.Proof.X25519.AArch64.wd m b (c + 8 * i)) % 2 ^ 64) (fun i => [a + 8 * i, c + 8 * i])
    (fun _ => True) (fun _ _ _ _ => trivial)
    (fun i hi s hs _ => VG.Proof.X25519.AArch64.addStep_ok hs (ho.off hi) (ha.off hi) (hc.off hi))
    (fun i _ m m' h => by rw [(VG.Proof.X25519.AArch64.val_congr2 h).1, (VG.Proof.X25519.AArch64.val_congr2 h).2]) (VG.Proof.X25519.AArch64.reads2 ha hc hoa hoc) hs trivial)
    fun s' ⟨e, f, k⟩ => ⟨?_, f, k⟩
  rw [e]
  funext i
  simp only [VG.Proof.X25519.AArch64.addF, VG.Proof.X25519.AArch64.limbs]
  split <;> rfl

/-! ## Differences -/

/-- One limb of `sub`, with the limb `P` of `16 p` in `preg i`. -/
theorem subStep_ok {b : Addr} {s : State} (hs : VG.Proof.X25519.AArch64.Sc b s) {o a c i : Nat} (ho : VG.Proof.X25519.AArch64.Off (o + 8 * i))
    (ha : VG.Proof.X25519.AArch64.Off (a + 8 * i)) (hc : VG.Proof.X25519.AArch64.Off (c + 8 * i)) {P : Nat} (hP : VG.Proof.X25519.AArch64.v s (preg i) = P) :
    WP isa (.block [ld .x17 (a + 8 * i), ld .x19 (c + 8 * i), .add .x .x17 .x17 (preg i),
        .sub .x .x17 .x17 .x19, st .x17 (o + 8 * i)]) s
      fun s' => ∃ x : BitVec 64, x.toNat = VG.Proof.X25519.AArch64.subL (VG.Proof.X25519.AArch64.wd s.mem b (a + 8 * i)) P (VG.Proof.X25519.AArch64.wd s.mem b (c + 8 * i)) ∧
        s'.mem = s.mem.writeW (b + BitVec.ofNat 64 (o + 8 * i)) x ∧ VG.Proof.X25519.AArch64.Kp [.x17, .x19] s s' := by
  have hp : preg i ≠ .x17 ∧ preg i ≠ .x19 ∧ preg i ≠ .x3 := by
    simp only [preg]; split <;> decide
  have hs1 := VG.Proof.X25519.AArch64.sc_wx s (s.mem.readW (b + BitVec.ofNat 64 (a + 8 * i)) 64) hs (show Reg.x17 ≠ .x3 by decide)
  have hs2 := VG.Proof.X25519.AArch64.sc_wx _ (s.mem.readW (b + BitVec.ofNat 64 (c + 8 * i)) 64) hs1 (show Reg.x19 ≠ .x3 by decide)
  apply WP.of_runBlock
  simp only [runBlock_cons, VG.Proof.X25519.AArch64.exec_ld hs _ ha, runStep_some, VG.Proof.X25519.AArch64.exec_ld hs1 _ hc, VG.Proof.X25519.AArch64.mem_wx, VG.Proof.X25519.AArch64.exec_add_x,
    VG.Proof.X25519.AArch64.exec_sub_x, VG.Proof.X25519.AArch64.gpr_wx_self, VG.Proof.X25519.AArch64.gpr_wx_ne _ _ (show Reg.x17 ≠ .x19 by decide), VG.Proof.X25519.AArch64.gpr_wx_ne _ _ hp.1,
    VG.Proof.X25519.AArch64.gpr_wx_ne _ _ hp.2.1]
  rw [VG.Proof.X25519.AArch64.exec_st (VG.Proof.X25519.AArch64.sc_wx _ _ (VG.Proof.X25519.AArch64.sc_wx _ _ hs2 (by decide)) (by decide)) _ ho]
  simp only [runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left', VG.Proof.X25519.AArch64.mem_wx, VG.Proof.X25519.AArch64.gpr_wx_self]
  refine ⟨_, ?_, rfl, ⟨fun r hr => ?_, rfl, rfl⟩⟩
  · rw [BitVec.toNat_sub, BitVec.toNat_add, VG.Proof.X25519.AArch64.gpr_wx_ne _ _ (show Reg.x19 ≠ .x17 by decide),
      VG.Proof.X25519.AArch64.gpr_wx_self, VG.Proof.X25519.AArch64.wd_def, VG.Proof.X25519.AArch64.wd_def, ← hP, VG.Proof.X25519.AArch64.v, VG.Proof.X25519.AArch64.subL]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    show (State.write _ _ _ _).gpr r = _
    rw [VG.Proof.X25519.AArch64.gpr_wx_ne _ _ hr.1, VG.Proof.X25519.AArch64.gpr_wx_ne _ _ hr.1, VG.Proof.X25519.AArch64.gpr_wx_ne _ _ hr.2, VG.Proof.X25519.AArch64.gpr_wx_ne _ _ hr.1]

theorem const16p_ok (s : State) :
    WP isa (.block const16p) s fun s' => VG.Proof.X25519.AArch64.v s' .x20 = VG.Proof.X25519.AArch64.p16 0 ∧ VG.Proof.X25519.AArch64.v s' .x21 = VG.Proof.X25519.AArch64.p16 1 ∧
      VG.Proof.X25519.AArch64.Kp [.x20, .x21] s s' ∧ s'.mem = s.mem := by
  apply WP.of_runBlock
  simp only [const16p, runBlock_cons, VG.Proof.X25519.AArch64.exec_movz, runStep_some, VG.Proof.X25519.AArch64.exec_movk1, runBlock_nil,
    Option.some.injEq, exists_eq_left', VG.Proof.X25519.AArch64.v, VG.Proof.X25519.AArch64.gpr_wx_self, VG.Proof.X25519.AArch64.gpr_wx_ne _ _ (show Reg.x20 ≠ .x21 by decide)]
  exact ⟨by decide, by decide,
    ((((VG.Proof.X25519.AArch64.kp_wx s _ _).trans (VG.Proof.X25519.AArch64.kp_wx _ _ _)).trans (VG.Proof.X25519.AArch64.kp_wx _ _ _)).trans (VG.Proof.X25519.AArch64.kp_wx _ _ _)).sub (by sub_regs), rfl⟩

theorem preg_p16 {s : State} (h0 : VG.Proof.X25519.AArch64.v s .x20 = VG.Proof.X25519.AArch64.p16 0) (h1 : VG.Proof.X25519.AArch64.v s .x21 = VG.Proof.X25519.AArch64.p16 1) (i : Nat) :
    VG.Proof.X25519.AArch64.v s (preg i) = VG.Proof.X25519.AArch64.p16 i := by
  simp only [preg, VG.Proof.X25519.AArch64.p16]; split
  · rename_i h; subst h; exact h0
  · rename_i h; rw [h1]; rfl

/-- `[o] = [a] + 16 p - [c]`. -/
theorem sub_ok {b : Addr} {s : State} (hs : VG.Proof.X25519.AArch64.Sc b s) {o a c : Nat} (ho : VG.Proof.X25519.AArch64.Slot o) (ha : VG.Proof.X25519.AArch64.Slot a)
    (hc : VG.Proof.X25519.AArch64.Slot c) (hoa : VG.Proof.X25519.AArch64.Alias o a) (hoc : VG.Proof.X25519.AArch64.Alias o c) :
    WP isa (.block (VG.Impl.X25519.AArch64.sub o a c)) s fun s' =>
      VG.Proof.X25519.AArch64.limbs s'.mem b o = VG.Proof.X25519.AArch64.subF (VG.Proof.X25519.AArch64.limbs s.mem b a) (VG.Proof.X25519.AArch64.limbs s.mem b c) ∧ Frame [VG.Proof.X25519.AArch64.slotR b o] s.mem s'.mem ∧
        VG.Proof.X25519.AArch64.Kp [.x20, .x21, .x17, .x19] s s' := by
  rw [VG.Impl.X25519.AArch64.sub]
  refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.const16p_ok s) fun s₁ ⟨e0, e1, k₁, m₁⟩ => ?_)
  refine WP.mono (VG.Proof.X25519.AArch64.limbwise_all ho _ [.x17, .x19] (by decide)
    (fun i m => VG.Proof.X25519.AArch64.subL (VG.Proof.X25519.AArch64.wd m b (a + 8 * i)) (VG.Proof.X25519.AArch64.p16 i) (VG.Proof.X25519.AArch64.wd m b (c + 8 * i))) (fun i => [a + 8 * i, c + 8 * i])
    (fun s => VG.Proof.X25519.AArch64.v s .x20 = VG.Proof.X25519.AArch64.p16 0 ∧ VG.Proof.X25519.AArch64.v s .x21 = VG.Proof.X25519.AArch64.p16 1)
    (fun s s' h k => ⟨by rw [VG.Proof.X25519.AArch64.v, k.gpr _ (by decide)]; exact h.1, by rw [VG.Proof.X25519.AArch64.v, k.gpr _ (by decide)]; exact h.2⟩)
    (fun i hi s hs hI => VG.Proof.X25519.AArch64.subStep_ok hs (ho.off hi) (ha.off hi) (hc.off hi) (VG.Proof.X25519.AArch64.preg_p16 hI.1 hI.2 i))
    (fun i _ m m' h => by rw [(VG.Proof.X25519.AArch64.val_congr2 h).1, (VG.Proof.X25519.AArch64.val_congr2 h).2]) (VG.Proof.X25519.AArch64.reads2 ha hc hoa hoc)
    (hs.of_kp k₁ (by decide)) ⟨e0, e1⟩)
    fun s' ⟨e, f, k⟩ => ⟨?_, by rw [← m₁]; exact f, k₁.trans k⟩
  rw [e, m₁]
  funext i
  simp only [VG.Proof.X25519.AArch64.subF, VG.Proof.X25519.AArch64.limbs]
  split <;> rfl

/-! ## Copies -/

theorem copyStep_ok {b : Addr} {s : State} (hs : VG.Proof.X25519.AArch64.Sc b s) {o a i : Nat} (ho : VG.Proof.X25519.AArch64.Off (o + 8 * i))
    (ha : VG.Proof.X25519.AArch64.Off (a + 8 * i)) :
    WP isa (.block [ld .x17 (a + 8 * i), st .x17 (o + 8 * i)]) s
      fun s' => ∃ x : BitVec 64, x.toNat = VG.Proof.X25519.AArch64.wd s.mem b (a + 8 * i) ∧
        s'.mem = s.mem.writeW (b + BitVec.ofNat 64 (o + 8 * i)) x ∧ VG.Proof.X25519.AArch64.Kp [.x17] s s' := by
  have hs1 := VG.Proof.X25519.AArch64.sc_wx s (s.mem.readW (b + BitVec.ofNat 64 (a + 8 * i)) 64) hs (show Reg.x17 ≠ .x3 by decide)
  apply WP.of_runBlock
  simp only [runBlock_cons, VG.Proof.X25519.AArch64.exec_ld hs _ ha, runStep_some]
  rw [VG.Proof.X25519.AArch64.exec_st hs1 _ ho]
  simp only [runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left', VG.Proof.X25519.AArch64.mem_wx, VG.Proof.X25519.AArch64.gpr_wx_self]
  exact ⟨_, rfl, rfl, ⟨fun r hr => VG.Proof.X25519.AArch64.gpr_wx_ne _ _ (by simpa using hr), rfl, rfl⟩⟩

/-- `[o] = [a]`. -/
theorem copy_ok {b : Addr} {s : State} (hs : VG.Proof.X25519.AArch64.Sc b s) {o a : Nat} (ho : VG.Proof.X25519.AArch64.Slot o) (ha : VG.Proof.X25519.AArch64.Slot a)
    (hoa : VG.Proof.X25519.AArch64.Alias o a) :
    WP isa (.block (copy o a)) s fun s' =>
      VG.Proof.X25519.AArch64.limbs s'.mem b o = VG.Proof.X25519.AArch64.limbs s.mem b a ∧ Frame [VG.Proof.X25519.AArch64.slotR b o] s.mem s'.mem ∧ VG.Proof.X25519.AArch64.Kp [.x17] s s' := by
  refine WP.mono (VG.Proof.X25519.AArch64.limbwise_all ho _ [.x17] (by decide) (fun i m => VG.Proof.X25519.AArch64.wd m b (a + 8 * i)) (fun i => [a + 8 * i])
    (fun _ => True) (fun _ _ _ _ => trivial)
    (fun i hi s hs _ => VG.Proof.X25519.AArch64.copyStep_ok hs (ho.off hi) (ha.off hi))
    (fun i _ m m' h => h _ (by simp)) (fun i hi off hoff => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
      subst hoff; exact ⟨ha.off hi, fun j hj => hoa.ne hi hj⟩) hs trivial)
    fun s' ⟨e, f, k⟩ => ⟨?_, f, k⟩
  rw [e]
  funext i
  simp only [VG.Proof.X25519.AArch64.limbs]

/-! ## Conditional swaps -/

/-- `x` if the mask `m` is zero, `y` if it is all ones. -/
def csel (m x y : BitVec 64) : BitVec 64 := x ^^^ ((x ^^^ y) &&& m)

theorem csel_zero (x y : BitVec 64) : VG.Proof.X25519.AArch64.csel 0 x y = x := by
  rw [VG.Proof.X25519.AArch64.csel, show (0 : BitVec 64) = 0#64 from rfl, BitVec.and_zero, BitVec.xor_zero]

theorem csel_ones (x y : BitVec 64) : VG.Proof.X25519.AArch64.csel (BitVec.allOnes 64) x y = y := by
  rw [VG.Proof.X25519.AArch64.csel, BitVec.and_allOnes, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-- The mask of `swap`: all ones if `sw`. -/
def maskB (sw : Bool) : BitVec 64 := if sw then BitVec.allOnes 64 else 0

theorem csel_mask (sw : Bool) (x y : BitVec 64) : VG.Proof.X25519.AArch64.csel (VG.Proof.X25519.AArch64.maskB sw) x y = if sw then y else x := by
  cases sw
  · exact VG.Proof.X25519.AArch64.csel_zero x y
  · exact VG.Proof.X25519.AArch64.csel_ones x y

theorem cswapStep_ok {b : Addr} {s : State} (hs : VG.Proof.X25519.AArch64.Sc b s) {x y i : Nat} (hx : VG.Proof.X25519.AArch64.Off (x + 8 * i))
    (hy : VG.Proof.X25519.AArch64.Off (y + 8 * i)) :
    WP isa (.block [ld .x17 (x + 8 * i), ld .x19 (y + 8 * i), .logic .eor .x .x20 .x17 .x19,
        .logic .and .x .x20 .x20 .x22, .logic .eor .x .x17 .x17 .x20, .logic .eor .x .x19 .x19 .x20,
        st .x17 (x + 8 * i), st .x19 (y + 8 * i)]) s fun s' =>
      s'.mem = (s.mem.writeW (b + BitVec.ofNat 64 (x + 8 * i))
          (VG.Proof.X25519.AArch64.csel (s.gpr .x22) (s.mem.readW (b + BitVec.ofNat 64 (x + 8 * i)) 64)
            (s.mem.readW (b + BitVec.ofNat 64 (y + 8 * i)) 64))).writeW (b + BitVec.ofNat 64 (y + 8 * i))
          (VG.Proof.X25519.AArch64.csel (s.gpr .x22) (s.mem.readW (b + BitVec.ofNat 64 (y + 8 * i)) 64)
            (s.mem.readW (b + BitVec.ofNat 64 (x + 8 * i)) 64)) ∧
        VG.Proof.X25519.AArch64.Kp [.x17, .x19, .x20] s s' := by
  have hs1 := VG.Proof.X25519.AArch64.sc_wx s (s.mem.readW (b + BitVec.ofNat 64 (x + 8 * i)) 64) hs (show Reg.x17 ≠ .x3 by decide)
  have h1 : WP isa (.block [ld .x17 (x + 8 * i), ld .x19 (y + 8 * i), .logic .eor .x .x20 .x17 .x19,
      .logic .and .x .x20 .x20 .x22, .logic .eor .x .x17 .x17 .x20, .logic .eor .x .x19 .x19 .x20]) s
      fun s₁ => s₁.gpr .x17 = VG.Proof.X25519.AArch64.csel (s.gpr .x22) (s.mem.readW (b + BitVec.ofNat 64 (x + 8 * i)) 64)
            (s.mem.readW (b + BitVec.ofNat 64 (y + 8 * i)) 64) ∧
        s₁.gpr .x19 = VG.Proof.X25519.AArch64.csel (s.gpr .x22) (s.mem.readW (b + BitVec.ofNat 64 (y + 8 * i)) 64)
            (s.mem.readW (b + BitVec.ofNat 64 (x + 8 * i)) 64) ∧
        VG.Proof.X25519.AArch64.Kp [.x17, .x19, .x20] s s₁ ∧ s₁.mem = s.mem := by
    apply WP.of_runBlock
    simp only [runBlock_cons, VG.Proof.X25519.AArch64.exec_ld hs _ hx, runStep_some, VG.Proof.X25519.AArch64.exec_ld hs1 _ hy, VG.Proof.X25519.AArch64.mem_wx, VG.Proof.X25519.AArch64.exec_eor_x,
      VG.Proof.X25519.AArch64.exec_and_x, runBlock_nil, Option.some.injEq, exists_eq_left', VG.Proof.X25519.AArch64.gpr_wx_self,
      VG.Proof.X25519.AArch64.gpr_wx_ne _ _ (show Reg.x17 ≠ .x19 by decide), VG.Proof.X25519.AArch64.gpr_wx_ne _ _ (show Reg.x19 ≠ .x17 by decide),
      VG.Proof.X25519.AArch64.gpr_wx_ne _ _ (show Reg.x17 ≠ .x20 by decide), VG.Proof.X25519.AArch64.gpr_wx_ne _ _ (show Reg.x19 ≠ .x20 by decide),
      VG.Proof.X25519.AArch64.gpr_wx_ne _ _ (show Reg.x20 ≠ .x17 by decide),
      VG.Proof.X25519.AArch64.gpr_wx_ne _ _ (show Reg.x22 ≠ .x17 by decide), VG.Proof.X25519.AArch64.gpr_wx_ne _ _ (show Reg.x22 ≠ .x19 by decide),
      VG.Proof.X25519.AArch64.gpr_wx_ne _ _ (show Reg.x22 ≠ .x20 by decide)]
    refine ⟨rfl, ?_, ⟨fun r hr => ?_, rfl, rfl⟩, trivial⟩
    · simp only [VG.Proof.X25519.AArch64.csel]
      generalize s.mem.readW (b + BitVec.ofNat 64 (x + 8 * i)) 64 = p
      generalize s.mem.readW (b + BitVec.ofNat 64 (y + 8 * i)) 64 = q
      generalize s.gpr Reg.x22 = m
      rw [BitVec.xor_comm q p]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [VG.Proof.X25519.AArch64.gpr_wx_ne _ _ hr.2.1, VG.Proof.X25519.AArch64.gpr_wx_ne _ _ hr.1, VG.Proof.X25519.AArch64.gpr_wx_ne _ _ hr.2.2, VG.Proof.X25519.AArch64.gpr_wx_ne _ _ hr.2.2,
        VG.Proof.X25519.AArch64.gpr_wx_ne _ _ hr.2.1, VG.Proof.X25519.AArch64.gpr_wx_ne _ _ hr.1]
  rw [show [ld .x17 (x + 8 * i), ld .x19 (y + 8 * i), .logic .eor .x .x20 .x17 .x19,
        .logic .and .x .x20 .x20 .x22, .logic .eor .x .x17 .x17 .x20, .logic .eor .x .x19 .x19 .x20,
        st .x17 (x + 8 * i), st .x19 (y + 8 * i)] =
      ([ld .x17 (x + 8 * i), ld .x19 (y + 8 * i), .logic .eor .x .x20 .x17 .x19,
        .logic .and .x .x20 .x20 .x22, .logic .eor .x .x17 .x17 .x20, .logic .eor .x .x19 .x19 .x20] : List Instr) ++
        ([st .x17 (x + 8 * i), st .x19 (y + 8 * i)] : List Instr) from rfl]
  refine WP.block_append (WP.mono h1 fun s₁ ⟨e17, e19, k₁, m₁⟩ => ?_)
  have hs₁ := hs.of_kp k₁ (by decide)
  apply WP.of_runBlock
  rw [runBlock_cons, VG.Proof.X25519.AArch64.exec_st hs₁ _ hx, runStep_some, runBlock_cons, VG.Proof.X25519.AArch64.exec_st (hs₁.mem _) _ hy,
    runStep_some, runBlock_nil]
  exact ⟨_, rfl, by rw [e17, e19, m₁], ⟨k₁.gpr, k₁.rd, k₁.wr⟩⟩

/-- The first `n` limbs of the swap of the elements at `x` and `y` by the mask `x22`. -/
theorem cswapN_ok {b : Addr} {x y : Nat} (hx : VG.Proof.X25519.AArch64.Slot x) (hy : VG.Proof.X25519.AArch64.Slot y)
    (hxy : x + 120 ≤ y ∨ y + 120 ≤ x) :
    ∀ n ≤ 15, ∀ s : State, VG.Proof.X25519.AArch64.Sc b s →
    WP isa (.block ((List.range n).flatMap fun i =>
      [ld .x17 (x + 8 * i), ld .x19 (y + 8 * i), .logic .eor .x .x20 .x17 .x19,
        .logic .and .x .x20 .x20 .x22, .logic .eor .x .x17 .x17 .x20, .logic .eor .x .x19 .x19 .x20,
        st .x17 (x + 8 * i), st .x19 (y + 8 * i)])) s fun s' =>
      (∀ k < n, VG.Proof.X25519.AArch64.wd s'.mem b (x + 8 * k) = (VG.Proof.X25519.AArch64.csel (s.gpr .x22) (s.mem.readW (b + BitVec.ofNat 64 (x + 8 * k)) 64)
          (s.mem.readW (b + BitVec.ofNat 64 (y + 8 * k)) 64)).toNat ∧
        VG.Proof.X25519.AArch64.wd s'.mem b (y + 8 * k) = (VG.Proof.X25519.AArch64.csel (s.gpr .x22) (s.mem.readW (b + BitVec.ofNat 64 (y + 8 * k)) 64)
          (s.mem.readW (b + BitVec.ofNat 64 (x + 8 * k)) 64)).toNat) ∧
      (∀ off, VG.Proof.X25519.AArch64.Off off → (∀ j < n, off ≠ x + 8 * j ∧ off ≠ y + 8 * j) → VG.Proof.X25519.AArch64.wd s'.mem b off = VG.Proof.X25519.AArch64.wd s.mem b off) ∧
      Frame [VG.Proof.X25519.AArch64.slotR b x, VG.Proof.X25519.AArch64.slotR b y] s.mem s'.mem ∧ VG.Proof.X25519.AArch64.Kp [.x17, .x19, .x20] s s'
  | 0, _, s, _ => WP.block_nil ⟨fun k hk => absurd hk (Nat.not_lt_zero _), fun _ _ _ => rfl,
      Frame.refl _ _, Kp.refl _ _⟩
  | n + 1, hn, s, hs => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.cswapN_ok hx hy hxy n (by omega) s hs) fun s₁ ⟨e₁, u₁, f₁, k₁⟩ => ?_)
    have hxn := hx.off (i := n) (by omega)
    have hyn := hy.off (i := n) (by omega)
    refine WP.mono (VG.Proof.X25519.AArch64.cswapStep_ok (hs.of_kp k₁ (by decide)) hxn hyn) fun s₂ ⟨m₂, k₂⟩ =>
      ⟨fun k hk => ?_, fun off hoff hj => ?_, ?_, (k₁.trans k₂).sub (List.append_subset.mpr
        ⟨List.Subset.refl _, List.Subset.refl _⟩)⟩
    · have g22 : s₁.gpr .x22 = s.gpr .x22 := k₁.gpr _ (by decide)
      have rx : s₁.mem.readW (b + BitVec.ofNat 64 (x + 8 * n)) 64 = s.mem.readW (b + BitVec.ofNat 64 (x + 8 * n)) 64 :=
        BitVec.eq_of_toNat_eq (u₁ _ hxn fun j hj => ⟨by omega, by omega⟩)
      have ry : s₁.mem.readW (b + BitVec.ofNat 64 (y + 8 * n)) 64 = s.mem.readW (b + BitVec.ofNat 64 (y + 8 * n)) 64 :=
        BitVec.eq_of_toNat_eq (u₁ _ hyn fun j hj => ⟨by omega, by omega⟩)
      rw [m₂, VG.Proof.X25519.AArch64.wd_writeW _ _ _ hyn (hx.off (by omega)), VG.Proof.X25519.AArch64.wd_writeW _ _ _ hxn (hx.off (by omega)),
        VG.Proof.X25519.AArch64.wd_writeW _ _ _ hyn (hy.off (by omega)), VG.Proof.X25519.AArch64.wd_writeW _ _ _ hxn (hy.off (by omega))]
      by_cases hkn : k = n
      · subst hkn
        rw [ite_eq_right (by omega), ite_eq_left rfl, ite_eq_left rfl, g22, rx, ry]
        exact ⟨rfl, rfl⟩
      · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
        exact e₁ k (by omega)
    · rw [m₂, VG.Proof.X25519.AArch64.wd_writeW _ _ _ hyn hoff, VG.Proof.X25519.AArch64.wd_writeW _ _ _ hxn hoff, ite_eq_right (hj n (by omega)).2,
        ite_eq_right (hj n (by omega)).1]
      exact u₁ off hoff fun j hjn => hj j (by omega)
    · rw [m₂]
      exact (f₁.writeW List.mem_cons_self _ (VG.Proof.X25519.AArch64.slot_contains b hx (by omega))).writeW
        (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ (VG.Proof.X25519.AArch64.slot_contains b hy (by omega))

/-- Swaps the elements at `x` and `y` if `sw` (the mask `x22` of `sw`). -/
theorem cswap_ok {b : Addr} {s : State} (hs : VG.Proof.X25519.AArch64.Sc b s) {x y : Nat} (hx : VG.Proof.X25519.AArch64.Slot x) (hy : VG.Proof.X25519.AArch64.Slot y)
    (hxy : x + 120 ≤ y ∨ y + 120 ≤ x) {sw : Bool} (hm : s.gpr .x22 = VG.Proof.X25519.AArch64.maskB sw) :
    WP isa (.block (cswap x y)) s fun s' =>
      VG.Proof.X25519.AArch64.limbs s'.mem b x = (if sw then VG.Proof.X25519.AArch64.limbs s.mem b y else VG.Proof.X25519.AArch64.limbs s.mem b x) ∧
      VG.Proof.X25519.AArch64.limbs s'.mem b y = (if sw then VG.Proof.X25519.AArch64.limbs s.mem b x else VG.Proof.X25519.AArch64.limbs s.mem b y) ∧
      Frame [VG.Proof.X25519.AArch64.slotR b x, VG.Proof.X25519.AArch64.slotR b y] s.mem s'.mem ∧ VG.Proof.X25519.AArch64.Kp [.x17, .x19, .x20] s s' :=
  WP.mono (VG.Proof.X25519.AArch64.cswapN_ok hx hy hxy 15 (by decide) s hs) fun s' ⟨e, _, f, k⟩ => ⟨funext fun i => by
    simp only [VG.Proof.X25519.AArch64.limbs]
    split
    · rename_i hi
      rw [(e i hi).1, hm, VG.Proof.X25519.AArch64.csel_mask]
      cases sw <;> simp only [Bool.false_eq_true, ite_false, ite_true, VG.Proof.X25519.AArch64.limbs, hi, VG.Proof.X25519.AArch64.wd_def]
    · rename_i hi
      cases sw <;> simp only [Bool.false_eq_true, ite_false, ite_true, VG.Proof.X25519.AArch64.limbs, hi], funext fun i => by
    simp only [VG.Proof.X25519.AArch64.limbs]
    split
    · rename_i hi
      rw [(e i hi).2, hm, VG.Proof.X25519.AArch64.csel_mask]
      cases sw <;> simp only [Bool.false_eq_true, ite_false, ite_true, VG.Proof.X25519.AArch64.limbs, hi, VG.Proof.X25519.AArch64.wd_def]
    · rename_i hi
      cases sw <;> simp only [Bool.false_eq_true, ite_false, ite_true, VG.Proof.X25519.AArch64.limbs, hi], f, k⟩

/-! ## Multiplication by `a24` -/

theorem scaleStep_ok {b : Addr} {s : State} (hs : VG.Proof.X25519.AArch64.Sc b s) {a k : Nat} (ha : VG.Proof.X25519.AArch64.Off (a + 8 * k)) (hk : k < 15) :
    WP isa (.block [ld .x17 (a + 8 * k), .mul .x (dreg k) .x17 .x20]) s fun s' =>
      VG.Proof.X25519.AArch64.v s' (dreg k) = VG.Proof.X25519.AArch64.wd s.mem b (a + 8 * k) * VG.Proof.X25519.AArch64.v s .x20 % 2 ^ 64 ∧ VG.Proof.X25519.AArch64.Kp [.x17, dreg k] s s' ∧
        s'.mem = s.mem := by
  obtain ⟨d17, -, d20, -⟩ := VG.Proof.X25519.AArch64.dreg_facts k hk
  apply WP.of_runBlock
  simp only [runBlock_cons, VG.Proof.X25519.AArch64.exec_ld hs _ ha, runStep_some, VG.Proof.X25519.AArch64.exec_mul_x, runBlock_nil, Option.some.injEq,
    exists_eq_left', VG.Proof.X25519.AArch64.mem_wx, VG.Proof.X25519.AArch64.v, VG.Proof.X25519.AArch64.gpr_wx_self, VG.Proof.X25519.AArch64.gpr_wx_ne _ _ (show Reg.x20 ≠ .x17 by decide)]
  refine ⟨by rw [BitVec.toNat_mul, VG.Proof.X25519.AArch64.wd_def], ⟨fun r hr => ?_, rfl, rfl⟩, trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  rw [VG.Proof.X25519.AArch64.gpr_wx_ne _ _ hr.2, VG.Proof.X25519.AArch64.gpr_wx_ne _ _ hr.1]

theorem scaleN_ok {b : Addr} {a : Nat} (ha : VG.Proof.X25519.AArch64.Slot a) :
    ∀ n ≤ 15, ∀ s : State, VG.Proof.X25519.AArch64.Sc b s →
    WP isa (.block ((List.range n).flatMap fun k => [ld .x17 (a + 8 * k), .mul .x (dreg k) .x17 .x20])) s
      fun s' => (∀ k < n, VG.Proof.X25519.AArch64.v s' (dreg k) = VG.Proof.X25519.AArch64.limbs s.mem b a k * VG.Proof.X25519.AArch64.v s .x20 % 2 ^ 64) ∧ VG.Proof.X25519.AArch64.Kp (DR ++ ([.x17] : List Reg)) s s' ∧
        s'.mem = s.mem
  | 0, _, s, _ => WP.block_nil ⟨fun k hk => absurd hk (Nat.not_lt_zero _), Kp.refl _ _, rfl⟩
  | n + 1, hn, s, hs => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.scaleN_ok ha n (by omega) s hs) fun s₁ ⟨e₁, k₁, m₁⟩ => ?_)
    refine WP.mono (VG.Proof.X25519.AArch64.scaleStep_ok (hs.of_kp k₁ (by decide)) (ha.off (i := n) (by omega)) (by omega))
      fun s₂ ⟨e₂, k₂, m₂⟩ => ⟨fun k hk => ?_, (k₁.trans k₂).sub (List.append_subset.mpr
        ⟨List.Subset.refl _, ?_⟩), m₂.trans m₁⟩
    · have h20 : s₁.gpr .x20 = s.gpr .x20 := k₁.gpr _ (by decide)
      by_cases hkn : k = n
      · subst hkn
        rw [e₂, m₁, VG.Proof.X25519.AArch64.v, h20]
        simp only [VG.Proof.X25519.AArch64.limbs, show k < 15 by omega, ite_true]
      · obtain ⟨d17, -⟩ := VG.Proof.X25519.AArch64.dreg_facts k (by omega)
        have hne := VG.Proof.X25519.AArch64.dreg_ne (j := k) (k := n) (by omega) (by omega) hkn
        rw [VG.Proof.X25519.AArch64.v, k₂.gpr _ (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨d17, hne⟩)]
        exact e₁ k (by omega)
    · have := VG.Proof.X25519.AArch64.dreg_mem n (by omega)
      simp only [List.cons_subset, List.nil_subset, and_true, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false, true_or, or_true, this]

theorem constA24_ok (s : State) :
    WP isa (.block constA24) s fun s' => VG.Proof.X25519.AArch64.v s' .x20 = 121665 ∧ VG.Proof.X25519.AArch64.Kp [.x20] s s' ∧ s'.mem = s.mem := by
  apply WP.of_runBlock
  simp only [constA24, runBlock_cons, VG.Proof.X25519.AArch64.exec_movz, runStep_some, VG.Proof.X25519.AArch64.exec_movk1, runBlock_nil,
    Option.some.injEq, exists_eq_left', VG.Proof.X25519.AArch64.v, VG.Proof.X25519.AArch64.gpr_wx_self]
  exact ⟨by decide, ((VG.Proof.X25519.AArch64.kp_wx s _ _).trans (VG.Proof.X25519.AArch64.kp_wx _ _ _)).sub (by sub_regs), rfl⟩

/-- `[o] = a24 · [a]`. -/
theorem mulSmall_ok {b : Addr} {s : State} (hs : VG.Proof.X25519.AArch64.Sc b s) {o a : Nat} (ho : VG.Proof.X25519.AArch64.Slot o) (ha : VG.Proof.X25519.AArch64.Slot a) :
    WP isa (.block (mulSmall o a)) s fun s' =>
      VG.Proof.X25519.AArch64.limbs s'.mem b o = VG.Proof.X25519.AArch64.mulSmallF (VG.Proof.X25519.AArch64.limbs s.mem b a) ∧ Frame [VG.Proof.X25519.AArch64.slotR b o] s.mem s'.mem ∧
        VG.Proof.X25519.AArch64.Kp VG.Proof.X25519.AArch64.fieldRegs s s' := by
  rw [mulSmall, List.append_assoc, List.append_assoc, List.append_assoc]
  refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.const19_ok s) fun s₁ ⟨e₁, k₁, m₁⟩ => ?_)
  refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.constA24_ok s₁) fun s₂ ⟨e₂, k₂, m₂⟩ => ?_)
  have hs₂ := (hs.of_kp k₁ (by decide)).of_kp k₂ (by decide)
  refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.scaleN_ok ha 15 (by decide) s₂ hs₂) fun s₃ ⟨e₃, k₃, m₃⟩ => ?_)
  have h19₃ : s₃.gpr .x21 = 19 := by rw [k₃.gpr _ (by decide), k₂.gpr _ (by decide), e₁]
  refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.carry_ok h19₃) fun s₄ ⟨e₄, k₄, m₄⟩ => ?_)
  refine WP.mono (VG.Proof.X25519.AArch64.store_ok ((hs₂.of_kp k₃ (by decide)).of_kp k₄ (by decide)) ho) fun s₅ ⟨e₅, f₅, k₅⟩ =>
    ⟨?_, ?_, ?_⟩
  · rw [e₅, e₄, VG.Proof.X25519.AArch64.mulSmallF]
    refine congrArg VG.Proof.X25519.AArch64.carryF (funext fun k => ?_)
    simp only [VG.Proof.X25519.AArch64.regs, VG.Proof.X25519.AArch64.scaleF]
    split
    · rename_i hk; rw [e₃ k hk, e₂, m₂, m₁]
    · rfl
  · rw [← m₁, ← m₂, ← m₃, ← m₄]; exact f₅
  · exact (k₁.trans (k₂.trans (k₃.trans (k₄.trans k₅)))).sub (List.append_subset.mpr ⟨by decide,
      List.append_subset.mpr ⟨by decide, List.append_subset.mpr ⟨List.subset_append_left _ _, by simp⟩⟩⟩)

end VG.Proof.X25519.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.AArch64.Slots`. -/
section

/-!
# X25519 on AArch64: the field elements in their slots

The elements live in the slots of the working space (`slot n`, `n < 15`); `Inv
b s₀ s vals bnds` says that each slot `n` with a bound `bnds n = some k`
stands for the field element `vals n` with limbs below `2^k`, and that since
`s₀` only the registers of the field operations and the slots have changed.
Each field operation updates `vals` and `bnds` at its result's slot.
-/

namespace VG.Proof.X25519.AArch64

open VG VG.AArch64 VG.Impl.X25519.AArch64 VG.Spec.X25519 VG.Proof.X25519

/-- The limbs `f` stand for `x`, and are below `2^k`. -/
def Rep (f : Nat → Nat) (x : Fe) (k : Nat) : Prop := VG.Proof.X25519.AArch64.Bnd f k ∧ toFe (VG.Proof.X25519.AArch64.val15 f) = x

/-- Every slot with a bound stands for its value. -/
def Sl (m : Mem) (b : Addr) (vals : Nat → Fe) (bnds : Nat → Option Nat) : Prop :=
  ∀ n < 15, ∀ k, bnds n = some k → VG.Proof.X25519.AArch64.Rep (VG.Proof.X25519.AArch64.limbs m b (slot n)) (vals n) k

/-- The area of the slots. -/
abbrev slotArea (b : Addr) : Region := ⟨b + BitVec.ofNat 64 64, 1920⟩

/-- Between the field operations. -/
structure Inv (b : Addr) (s₀ s : State) (vals : Nat → Fe) (bnds : Nat → Option Nat) : Prop where
  sc : VG.Proof.X25519.AArch64.Sc b s
  sl : VG.Proof.X25519.AArch64.Sl s.mem b vals bnds
  kp : VG.Proof.X25519.AArch64.Kp VG.Proof.X25519.AArch64.fieldRegs s₀ s
  fr : Frame [VG.Proof.X25519.AArch64.slotArea b] s₀.mem s.mem

theorem slot_ok {n : Nat} (hn : n < 15) : VG.Proof.X25519.AArch64.Slot (slot n) := by
  simp only [VG.Proof.X25519.AArch64.Slot, slot]; omega

theorem slot_alias (o a : Nat) : VG.Proof.X25519.AArch64.Alias (slot o) (slot a) := by
  simp only [VG.Proof.X25519.AArch64.Alias, slot]; omega

theorem slotR_sub (b : Addr) {n : Nat} (hn : n < 15) : Region.Sub (VG.Proof.X25519.AArch64.slotR b (slot n)) (VG.Proof.X25519.AArch64.slotArea b) :=
  Offset.sub b (by simp only [slot]; omega) (by simp only [slot]; omega)

theorem slotR_disjoint (b : Addr) {n n' : Nat} (hn : n < 15) (hn' : n' < 15) (h : n ≠ n') :
    (VG.Proof.X25519.AArch64.slotR b (slot n)).Disjoint (VG.Proof.X25519.AArch64.slotR b (slot n')) :=
  Offset.disjoint b (by simp only [slot]; omega) (by simp only [slot]; omega) (by simp only [slot]; omega)

/-- The limbs of an element outside a frame's regions. -/
theorem limbs_frame {b : Addr} {o : Nat} (ho : VG.Proof.X25519.AArch64.Slot o) {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (VG.Proof.X25519.AArch64.slotR b o).Disjoint r) : VG.Proof.X25519.AArch64.limbs m' b o = VG.Proof.X25519.AArch64.limbs m b o := funext fun i => by
  simp only [VG.Proof.X25519.AArch64.limbs]
  split
  · rename_i hi
    simp only [VG.Proof.X25519.AArch64.wd]
    rw [hf.readW (VG.Proof.X25519.AArch64.slot_contains b ho hi) hd (by decide)]
  · rfl

theorem frame_slot {b : Addr} {s₀ s s' : State} (hf : Frame [VG.Proof.X25519.AArch64.slotArea b] s₀.mem s.mem) {n : Nat}
    (hn : n < 15) (h : Frame [VG.Proof.X25519.AArch64.slotR b (slot n)] s.mem s'.mem) : Frame [VG.Proof.X25519.AArch64.slotArea b] s₀.mem s'.mem :=
  hf.trans (h.sub fun r hr => ⟨VG.Proof.X25519.AArch64.slotArea b, List.mem_singleton_self _, by
    rw [List.mem_singleton.mp hr]; exact VG.Proof.X25519.AArch64.slotR_sub b hn⟩)

theorem limbs_other {b : Addr} {s s' : State} {o n : Nat} (ho : o < 15) (hn : n < 15) (h : n ≠ o)
    (hf : Frame [VG.Proof.X25519.AArch64.slotR b (slot o)] s.mem s'.mem) : VG.Proof.X25519.AArch64.limbs s'.mem b (slot n) = VG.Proof.X25519.AArch64.limbs s.mem b (slot n) :=
  VG.Proof.X25519.AArch64.limbs_frame (VG.Proof.X25519.AArch64.slot_ok hn) hf fun r hr => by
    rw [List.mem_singleton.mp hr]; exact VG.Proof.X25519.AArch64.slotR_disjoint b hn ho h

/-- A slot updated with a new value and bound. -/
theorem Sl.update {m m' : Mem} {b : Addr} {vals : Nat → Fe} {bnds : Nat → Option Nat} (h : VG.Proof.X25519.AArch64.Sl m b vals bnds)
    {o : Nat} (x : Fe) (k : Nat) (ho : VG.Proof.X25519.AArch64.Rep (VG.Proof.X25519.AArch64.limbs m' b (slot o)) x k)
    (hother : ∀ n < 15, n ≠ o → VG.Proof.X25519.AArch64.limbs m' b (slot n) = VG.Proof.X25519.AArch64.limbs m b (slot n)) :
    VG.Proof.X25519.AArch64.Sl m' b (Function.update vals o x) (Function.update bnds o (some k)) := by
  intro n hn j hj
  by_cases hno : n = o
  · subst hno
    rw [Function.update_self] at hj ⊢
    cases hj
    exact ho
  · rw [Function.update_of_ne hno] at hj ⊢
    rw [hother n hn hno]
    exact h n hn j hj

theorem Sl.bnd {m : Mem} {b : Addr} {vals : Nat → Fe} {bnds : Nat → Option Nat} (h : VG.Proof.X25519.AArch64.Sl m b vals bnds)
    {n k k' : Nat} (hn : n < 15) (hk : bnds n = some k) (hkk : k ≤ k') :
    VG.Proof.X25519.AArch64.Bnd (VG.Proof.X25519.AArch64.limbs m b (slot n)) k' ∧ toFe (VG.Proof.X25519.AArch64.val15 (VG.Proof.X25519.AArch64.limbs m b (slot n))) = vals n :=
  ⟨(h n hn k hk).1.mono hkk, (h n hn k hk).2⟩

theorem Inv.kp_sub {b : Addr} {s₀ s s' : State} {vals : Nat → Fe} {bnds : Nat → Option Nat}
    (h : VG.Proof.X25519.AArch64.Inv b s₀ s vals bnds) {W : List Reg} (k : VG.Proof.X25519.AArch64.Kp W s s') (hW : W ⊆ VG.Proof.X25519.AArch64.fieldRegs) : VG.Proof.X25519.AArch64.Kp VG.Proof.X25519.AArch64.fieldRegs s₀ s' :=
  (h.kp.trans (k.sub hW)).sub (List.append_subset.mpr ⟨List.Subset.refl _, List.Subset.refl _⟩)

/-! ## The operations on slots -/

theorem mul_inv {b : Addr} {s₀ s : State} {vals : Nat → Fe} {bnds : Nat → Option Nat}
    (h : VG.Proof.X25519.AArch64.Inv b s₀ s vals bnds) {o a c : Nat} (ho : o < 15) (ha : a < 15) (hc : c < 15) {ka kc : Nat}
    (hka : bnds a = some ka) (hkc : bnds c = some kc) (hka' : ka ≤ 26) (hkc' : kc ≤ 26) :
    WP isa (.block (mul (slot o) (slot a) (slot c))) s fun s' =>
      VG.Proof.X25519.AArch64.Inv b s₀ s' (Function.update vals o (vals a * vals c)) (Function.update bnds o (some 18)) :=
  WP.mono (VG.Proof.X25519.AArch64.mul_ok h.sc (VG.Proof.X25519.AArch64.slot_ok ho) (VG.Proof.X25519.AArch64.slot_ok ha) (VG.Proof.X25519.AArch64.slot_ok hc)) fun s' ⟨e, f, k⟩ =>
    ⟨h.sc.of_kp k (by decide), h.sl.update _ _ (by
      obtain ⟨b1, v1⟩ := h.sl.bnd ha hka hka'
      obtain ⟨b2, v2⟩ := h.sl.bnd hc hkc hkc'
      obtain ⟨r1, r2⟩ := VG.Proof.X25519.AArch64.mulF_spec b1 b2
      rw [e]; exact ⟨r1, by rw [r2, v1, v2]⟩) fun n hn hno => VG.Proof.X25519.AArch64.limbs_other ho hn hno f,
    h.kp_sub k (List.Subset.refl _), VG.Proof.X25519.AArch64.frame_slot h.fr ho f⟩

theorem mulSmall_inv {b : Addr} {s₀ s : State} {vals : Nat → Fe} {bnds : Nat → Option Nat}
    (h : VG.Proof.X25519.AArch64.Inv b s₀ s vals bnds) {o a : Nat} (ho : o < 15) (ha : a < 15) {ka : Nat}
    (hka : bnds a = some ka) (hka' : ka ≤ 26) :
    WP isa (.block (mulSmall (slot o) (slot a))) s fun s' =>
      VG.Proof.X25519.AArch64.Inv b s₀ s' (Function.update vals o (a24 * vals a)) (Function.update bnds o (some 18)) :=
  WP.mono (VG.Proof.X25519.AArch64.mulSmall_ok h.sc (VG.Proof.X25519.AArch64.slot_ok ho) (VG.Proof.X25519.AArch64.slot_ok ha)) fun s' ⟨e, f, k⟩ =>
    ⟨h.sc.of_kp k (by decide), h.sl.update _ _ (by
      obtain ⟨b1, v1⟩ := h.sl.bnd ha hka hka'
      obtain ⟨r1, r2⟩ := VG.Proof.X25519.AArch64.mulSmallF_spec b1
      rw [e]; exact ⟨r1, by rw [r2, v1]⟩) fun n hn hno => VG.Proof.X25519.AArch64.limbs_other ho hn hno f,
    h.kp_sub k (List.Subset.refl _), VG.Proof.X25519.AArch64.frame_slot h.fr ho f⟩

theorem add_inv {b : Addr} {s₀ s : State} {vals : Nat → Fe} {bnds : Nat → Option Nat}
    (h : VG.Proof.X25519.AArch64.Inv b s₀ s vals bnds) {o a c : Nat} (ho : o < 15) (ha : a < 15) (hc : c < 15) {ka kc : Nat}
    (hka : bnds a = some ka) (hkc : bnds c = some kc) (hka' : ka ≤ 25) (hkc' : kc ≤ 25) :
    WP isa (.block (add (slot o) (slot a) (slot c))) s fun s' =>
      VG.Proof.X25519.AArch64.Inv b s₀ s' (Function.update vals o (vals a + vals c)) (Function.update bnds o (some 26)) :=
  WP.mono (VG.Proof.X25519.AArch64.add_ok h.sc (VG.Proof.X25519.AArch64.slot_ok ho) (VG.Proof.X25519.AArch64.slot_ok ha) (VG.Proof.X25519.AArch64.slot_ok hc) (VG.Proof.X25519.AArch64.slot_alias o a) (VG.Proof.X25519.AArch64.slot_alias o c))
    fun s' ⟨e, f, k⟩ =>
    ⟨h.sc.of_kp k (by decide), h.sl.update _ _ (by
      obtain ⟨b1, v1⟩ := h.sl.bnd ha hka hka'
      obtain ⟨b2, v2⟩ := h.sl.bnd hc hkc hkc'
      obtain ⟨r1, r2⟩ := VG.Proof.X25519.AArch64.addF_spec b1 b2 (by decide) (Nat.le_refl _)
      rw [e]; exact ⟨r1, by rw [r2, v1, v2]⟩) fun n hn hno => VG.Proof.X25519.AArch64.limbs_other ho hn hno f,
    h.kp_sub k (by decide), VG.Proof.X25519.AArch64.frame_slot h.fr ho f⟩

theorem sub_inv {b : Addr} {s₀ s : State} {vals : Nat → Fe} {bnds : Nat → Option Nat}
    (h : VG.Proof.X25519.AArch64.Inv b s₀ s vals bnds) {o a c : Nat} (ho : o < 15) (ha : a < 15) (hc : c < 15) {ka kc : Nat}
    (hka : bnds a = some ka) (hkc : bnds c = some kc) (hka' : ka ≤ 21) (hkc' : kc ≤ 20) :
    WP isa (.block (VG.Impl.X25519.AArch64.sub (slot o) (slot a) (slot c))) s fun s' =>
      VG.Proof.X25519.AArch64.Inv b s₀ s' (Function.update vals o (vals a - vals c)) (Function.update bnds o (some 26)) :=
  WP.mono (VG.Proof.X25519.AArch64.sub_ok h.sc (VG.Proof.X25519.AArch64.slot_ok ho) (VG.Proof.X25519.AArch64.slot_ok ha) (VG.Proof.X25519.AArch64.slot_ok hc) (VG.Proof.X25519.AArch64.slot_alias o a) (VG.Proof.X25519.AArch64.slot_alias o c))
    fun s' ⟨e, f, k⟩ =>
    ⟨h.sc.of_kp k (by decide), h.sl.update _ _ (by
      obtain ⟨b1, v1⟩ := h.sl.bnd ha hka hka'
      obtain ⟨b2, v2⟩ := h.sl.bnd hc hkc hkc'
      obtain ⟨r1, r2⟩ := VG.Proof.X25519.AArch64.subF_spec b1 b2 (Nat.le_refl _) (by decide)
      rw [e]; exact ⟨r1.mono (by decide), by rw [r2, v1, v2]⟩) fun n hn hno => VG.Proof.X25519.AArch64.limbs_other ho hn hno f,
    h.kp_sub k (by decide), VG.Proof.X25519.AArch64.frame_slot h.fr ho f⟩

theorem copy_inv {b : Addr} {s₀ s : State} {vals : Nat → Fe} {bnds : Nat → Option Nat}
    (h : VG.Proof.X25519.AArch64.Inv b s₀ s vals bnds) {o a : Nat} (ho : o < 15) (ha : a < 15) {ka : Nat}
    (hka : bnds a = some ka) :
    WP isa (.block (copy (slot o) (slot a))) s fun s' =>
      VG.Proof.X25519.AArch64.Inv b s₀ s' (Function.update vals o (vals a)) (Function.update bnds o (some ka)) :=
  WP.mono (VG.Proof.X25519.AArch64.copy_ok h.sc (VG.Proof.X25519.AArch64.slot_ok ho) (VG.Proof.X25519.AArch64.slot_ok ha) (VG.Proof.X25519.AArch64.slot_alias o a)) fun s' ⟨e, f, k⟩ =>
    ⟨h.sc.of_kp k (by decide), h.sl.update _ _ (by rw [e]; exact h.sl a ha ka hka)
      fun n hn hno => VG.Proof.X25519.AArch64.limbs_other ho hn hno f,
    h.kp_sub k (by decide), VG.Proof.X25519.AArch64.frame_slot h.fr ho f⟩

theorem cswap_inv {b : Addr} {s₀ s : State} {vals : Nat → Fe} {bnds : Nat → Option Nat}
    (h : VG.Proof.X25519.AArch64.Inv b s₀ s vals bnds) {x y : Nat} (hx : x < 15) (hy : y < 15) (hxy : x ≠ y) {k : Nat}
    (hkx : bnds x = some k) (hky : bnds y = some k) {sw : Nat} (hm : s.gpr .x22 = VG.Proof.X25519.AArch64.maskB (sw == 1)) :
    WP isa (.block (cswap (slot x) (slot y))) s fun s' =>
      VG.Proof.X25519.AArch64.Inv b s₀ s' (Function.update (Function.update vals x (cswap sw (vals x) (vals y)).1) y
        (cswap sw (vals x) (vals y)).2) bnds ∧ s'.gpr .x22 = s.gpr .x22 := by
  refine WP.mono (VG.Proof.X25519.AArch64.cswap_ok h.sc (VG.Proof.X25519.AArch64.slot_ok hx) (VG.Proof.X25519.AArch64.slot_ok hy) (by simp only [slot]; omega) hm)
    fun s' ⟨ex, ey, f, kp⟩ => ⟨⟨h.sc.of_kp kp (by decide), ?_, h.kp_sub kp (by decide), ?_⟩,
      kp.gpr _ (by decide)⟩
  · intro n hn j hj
    have rx := h.sl x hx k hkx
    have ry := h.sl y hy k hky
    have csw : ∀ a c : Fe, cswap sw a c = if (sw == 1) = true then (c, a) else (a, c) := fun a c => by
      simp only [Spec.X25519.cswap, beq_iff_eq]
    by_cases hny : n = y
    · subst hny
      rw [Function.update_self, ey, csw]
      have hjk : j = k := Option.some.inj (hj.symm.trans hky)
      subst hjk
      cases (sw == 1)
      · rw [ite_eq_right (by decide), ite_eq_right (by decide)]; exact ry
      · rw [ite_eq_left rfl, ite_eq_left rfl]; exact rx
    · rw [Function.update_of_ne hny]
      by_cases hnx : n = x
      · subst hnx
        rw [Function.update_self, ex, csw]
        have hjk : j = k := Option.some.inj (hj.symm.trans hkx)
        subst hjk
        cases (sw == 1)
        · rw [ite_eq_right (by decide), ite_eq_right (by decide)]; exact rx
        · rw [ite_eq_left rfl, ite_eq_left rfl]; exact ry
      · rw [Function.update_of_ne hnx]
        rw [VG.Proof.X25519.AArch64.limbs_frame (VG.Proof.X25519.AArch64.slot_ok hn) f fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact VG.Proof.X25519.AArch64.slotR_disjoint b hn hx hnx
          · exact VG.Proof.X25519.AArch64.slotR_disjoint b hn hy hny]
        exact h.sl n hn j hj
  · exact h.fr.trans (f.sub fun r hr => ⟨VG.Proof.X25519.AArch64.slotArea b, List.mem_singleton_self _, by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact VG.Proof.X25519.AArch64.slotR_sub b hx
      · exact VG.Proof.X25519.AArch64.slotR_sub b hy⟩)

end VG.Proof.X25519.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.AArch64.Ladder`. -/
section

/-!
# X25519 on AArch64: the ladder

One iteration of the ladder (`step`) takes the ladder's variables in their
slots from `ladderAfter k x1 (t + 1)` to `ladderAfter k x1 t`, for the bit `t`
of the scalar stored at `BITS + t`; the loop (`ladder`) runs it for `t = 254,
…, 0`.
-/

namespace VG.Proof.X25519.AArch64

open VG VG.AArch64 VG.Impl.X25519.AArch64 VG.Spec.X25519 VG.Proof.X25519

/-! ## The bit and the mask -/

theorem maskB_of {x : Nat} (hx : x ≤ 1) :
    (0 : BitVec 64) - BitVec.ofNat 64 x = VG.Proof.X25519.AArch64.maskB (x == 1) := by
  rcases (by omega : x = 0 ∨ x = 1) with rfl | rfl <;> decide

theorem xor_le {a c : Nat} (ha : a ≤ 1) (hc : c ≤ 1) : a ^^^ c ≤ 1 := by
  rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl <;> rcases (by omega : c = 0 ∨ c = 1) with rfl | rfl <;>
    decide

theorem ofNat_xor {a c : Nat} (ha : a ≤ 1) (hc : c ≤ 1) :
    BitVec.ofNat 64 a ^^^ BitVec.ofNat 64 c = BitVec.ofNat 64 (a ^^^ c) := by
  rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl <;> rcases (by omega : c = 0 ∨ c = 1) with rfl | rfl <;>
    decide

/-- The address of bit `t`. -/
theorem bit_addr (b : Addr) (t : Nat) :
    b + BitVec.ofNat 64 t + BitVec.ofNat 64 BITS = b + BitVec.ofNat 64 (BITS + t) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_comm]

theorem bit_in {b : Addr} {s : State} (hs : VG.Proof.X25519.AArch64.Sc b s) {t : Nat} (ht : t < 255) :
    InRegions (s.rd ++ s.wr) (b + BitVec.ofNat 64 (BITS + t)) 1 :=
  ⟨VG.Proof.X25519.AArch64.scR b, List.mem_append_right _ hs.wr, Offset.contains_base b (by simp only [BITS, slot, NSLOT]; omega)
    (by simp only [BITS, slot, NSLOT]; omega)⟩

/-- The start of an iteration: the bit `k_t` from `BITS`, `swap ^ k_t` into
`x20`, its mask into `x22`, and `swap = k_t`. -/
theorem head_ok {b : Addr} {s : State} (hs : VG.Proof.X25519.AArch64.Sc b s) {t sw kt : Nat} (ht : t < 255) (hsw : sw ≤ 1)
    (hkt : kt ≤ 1) (h23 : s.gpr .x23 = BitVec.ofNat 64 (t + 1)) (h24 : s.gpr .x24 = BitVec.ofNat 64 sw)
    (hbit : s.mem (b + BitVec.ofNat 64 (BITS + t)) = BitVec.ofNat 8 kt) :
    WP isa (.block (([.subImm .x .x23 .x23 1, .add .x .x17 .x3 .x23, .ldrb .x19 .x17 BITS,
        .logic .eor .x .x20 .x24 .x19, .addImm .x .x24 .x19 0] : List Instr) ++ maskOf)) s fun s' =>
      s'.gpr .x23 = BitVec.ofNat 64 t ∧ s'.gpr .x24 = BitVec.ofNat 64 kt ∧
      s'.gpr .x22 = VG.Proof.X25519.AArch64.maskB ((sw ^^^ kt) == 1) ∧ VG.Proof.X25519.AArch64.Kp [.x23, .x17, .x19, .x20, .x24, .x22] s s' ∧
      s'.mem = s.mem := by
  have e23 : s.gpr .x23 - BitVec.ofNat 64 1 = BitVec.ofNat 64 t := by
    rw [h23, BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega), Nat.add_sub_cancel]
  have h1 : WP isa (.block [.subImm .x .x23 .x23 1, .add .x .x17 .x3 .x23]) s fun s₁ =>
      s₁.gpr .x23 = BitVec.ofNat 64 t ∧ s₁.gpr .x17 = b + BitVec.ofNat 64 t ∧ VG.Proof.X25519.AArch64.Kp [.x23, .x17] s s₁ ∧
        s₁.mem = s.mem := by
    apply WP.of_runBlock
    simp only [runBlock_cons, exec_subImm_x (show 1 < 4096 by decide), runStep_some, VG.Proof.X25519.AArch64.exec_add_x, VG.Proof.X25519.AArch64.read_x,
      VG.Proof.X25519.AArch64.gpr_wx_self, VG.Proof.X25519.AArch64.gpr_wx_ne _ _ (show Reg.x3 ≠ .x23 by decide), runBlock_nil, Option.some.injEq,
      exists_eq_left', VG.Proof.X25519.AArch64.gpr_wx_ne _ _ (show Reg.x23 ≠ .x17 by decide), hs.x3, e23]
    exact ⟨trivial, trivial, ((VG.Proof.X25519.AArch64.kp_wx s _ _).trans (VG.Proof.X25519.AArch64.kp_wx _ _ _)).sub (by sub_regs), rfl⟩
  rw [show ([.subImm .x .x23 .x23 1, .add .x .x17 .x3 .x23, .ldrb .x19 .x17 BITS,
        .logic .eor .x .x20 .x24 .x19, .addImm .x .x24 .x19 0] ++ maskOf : List Instr) =
      ([.subImm .x .x23 .x23 1, .add .x .x17 .x3 .x23] : List Instr) ++
      ([.ldrb .x19 .x17 BITS, .logic .eor .x .x20 .x24 .x19, .addImm .x .x24 .x19 0,
        .movz .x .x22 0 0, .sub .x .x22 .x22 .x20] : List Instr) from rfl]
  refine WP.block_append (WP.mono h1 fun s₁ ⟨e₁, f₁, k₁, m₁⟩ => ?_)
  have hs₁ := hs.of_kp k₁ (by decide)
  have h24₁ : s₁.gpr .x24 = BitVec.ofNat 64 sw := by rw [k₁.gpr _ (by decide), h24]
  apply WP.of_runBlock
  rw [runBlock_cons, VG.Proof.X25519.AArch64.exec_ldrb (by decide) (by rw [f₁, VG.Proof.X25519.AArch64.bit_addr]; exact VG.Proof.X25519.AArch64.bit_in hs₁ ht), runStep_some]
  have hk : ((s₁.mem.read (b + BitVec.ofNat 64 (BITS + t)) 1).setWidth 32).setWidth 64 = BitVec.ofNat 64 kt := by
    rw [VG.Proof.X25519.AArch64.read1_toNat, m₁, hbit]
    rcases (by omega : kt = 0 ∨ kt = 1) with rfl | rfl <;> rfl
  simp only [runBlock_cons, runStep_some, VG.Proof.X25519.AArch64.exec_eor_x, exec_addImm_x (show 0 < 4096 by decide), VG.Proof.X25519.AArch64.exec_movz,
    VG.Proof.X25519.AArch64.exec_sub_x, VG.Proof.X25519.AArch64.read_x, runBlock_nil, Option.some.injEq, exists_eq_left', f₁, VG.Proof.X25519.AArch64.bit_addr, VG.Proof.X25519.AArch64.gpr_wx_self,
    VG.Proof.X25519.AArch64.gpr_ww_self, VG.Proof.X25519.AArch64.gpr_wx_ne _ _ (show Reg.x23 ≠ .x22 by decide), VG.Proof.X25519.AArch64.gpr_wx_ne _ _ (show Reg.x24 ≠ .x22 by decide),
    VG.Proof.X25519.AArch64.gpr_wx_ne _ _ (show Reg.x20 ≠ .x22 by decide), VG.Proof.X25519.AArch64.gpr_wx_ne _ _ (show Reg.x20 ≠ .x24 by decide),
    VG.Proof.X25519.AArch64.gpr_wx_ne _ _ (show Reg.x19 ≠ .x20 by decide),
    VG.Proof.X25519.AArch64.gpr_wx_ne _ _ (show Reg.x23 ≠ .x24 by decide), VG.Proof.X25519.AArch64.gpr_wx_ne _ _ (show Reg.x23 ≠ .x20 by decide),
    VG.Proof.X25519.AArch64.gpr_ww_ne _ _ (show Reg.x23 ≠ .x19 by decide), VG.Proof.X25519.AArch64.gpr_ww_ne _ _ (show Reg.x24 ≠ .x19 by decide), hk, e₁, h24₁]
  refine ⟨trivial, by rw [BitVec.add_zero], ?_, ?_, ?_⟩
  · rw [VG.Proof.X25519.AArch64.ofNat_xor hsw hkt, show BitVec.setWidth 64 (0 : BitVec 16) = 0 from rfl, VG.Proof.X25519.AArch64.maskB_of (VG.Proof.X25519.AArch64.xor_le hsw hkt)]
  · exact (k₁.trans ((((VG.Proof.X25519.AArch64.kp_ww _ _ _).trans (VG.Proof.X25519.AArch64.kp_wx _ _ _)).trans (VG.Proof.X25519.AArch64.kp_wx _ _ _)).trans
      ((VG.Proof.X25519.AArch64.kp_wx _ _ _).trans (VG.Proof.X25519.AArch64.kp_wx _ _ _)))).sub (by sub_regs)
  · simp only [VG.Proof.X25519.AArch64.mem_wx, VG.Proof.X25519.AArch64.mem_ww, m₁]

end VG.Proof.X25519.AArch64

namespace VG.Proof.X25519.AArch64

open VG VG.AArch64 VG.Impl.X25519.AArch64 VG.Spec.X25519 VG.Proof.X25519

/-! ## One iteration -/

/-- The ladder's variables in their slots: `x_1, x_2, z_2, x_3, z_3` in slots 0 to 4. -/
def lvals (x1 : Fe) (st : Ladder) (n : Nat) : Fe :=
  if n = 0 then x1 else if n = 1 then st.x2 else if n = 2 then st.z2 else if n = 3 then st.x3 else st.z3

/-- Slots 0 to 4 have limbs below `2¹⁸`. -/
def lbnds (n : Nat) : Option Nat := if n < 5 then some 18 else none

theorem Sl.weaken {m : Mem} {b : Addr} {vals vals' : Nat → Fe} {bnds bnds' : Nat → Option Nat}
    (h : VG.Proof.X25519.AArch64.Sl m b vals bnds) (hw : ∀ n < 15, ∀ j, bnds' n = some j → bnds n = some j ∧ vals' n = vals n) :
    VG.Proof.X25519.AArch64.Sl m b vals' bnds' := fun n hn j hj => by
  obtain ⟨h1, h2⟩ := hw n hn j hj
  rw [h2]; exact h n hn j h1

/-- Evaluates the slots' values after an operation, so that they refer to the
earlier ones only through their values. -/
macro "vsimp" " at " h:ident : tactic => `(tactic| simp only [Function.update_apply, lvals, ite_true, ite_false,
  Nat.reduceEqDiff] at $h:ident)

/-- The field operations of an iteration, after the swaps' mask `x22`. -/
theorem ops_ok {b : Addr} {s₀ s : State} {x1 : Fe} {st : Ladder} (h : VG.Proof.X25519.AArch64.Inv b s₀ s (VG.Proof.X25519.AArch64.lvals x1 st) VG.Proof.X25519.AArch64.lbnds)
    {sw : Nat} (hm : s.gpr .x22 = VG.Proof.X25519.AArch64.maskB (sw == 1)) :
    WP isa (.block (cswap X2 X3 ++ cswap Z2 Z3 ++
      add A X2 Z2 ++ mul AA A A ++ VG.Impl.X25519.AArch64.sub B X2 Z2 ++ mul BB B B ++ VG.Impl.X25519.AArch64.sub E AA BB ++
      add C X3 Z3 ++ VG.Impl.X25519.AArch64.sub D X3 Z3 ++ mul DA D A ++ mul CB C B ++
      add X3 DA CB ++ mul X3 X3 X3 ++ VG.Impl.X25519.AArch64.sub Z3 DA CB ++ mul Z3 Z3 Z3 ++ mul Z3 X1 Z3 ++
      mul X2 AA BB ++ mulSmall Z2 E ++ add Z2 AA Z2 ++ mul Z2 E Z2)) s fun s' =>
      let x2 := (cswap sw st.x2 st.x3).1
      let x3 := (cswap sw st.x2 st.x3).2
      let z2 := (cswap sw st.z2 st.z3).1
      let z3 := (cswap sw st.z2 st.z3).2
      let A := x2 + z2
      let AA := A * A
      let B := x2 - z2
      let BB := B * B
      let E := AA - BB
      let C := x3 + z3
      let D := x3 - z3
      let DA := D * A
      let CB := C * B
      VG.Proof.X25519.AArch64.Inv b s₀ s' (VG.Proof.X25519.AArch64.lvals x1 ⟨AA * BB, E * (AA + a24 * E), (DA + CB) * (DA + CB),
        x1 * ((DA - CB) * (DA - CB)), 0⟩) VG.Proof.X25519.AArch64.lbnds := by
  simp only [X1, X2, Z2, X3, Z3, A, B, C, D, AA, BB, E, DA, CB, List.append_assoc]
  refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.cswap_inv h (x := 1) (y := 3) (by decide) (by decide) (by decide)
    (k := 18) rfl rfl hm) fun s₁ ⟨h₁, g₁⟩ => ?_)
  vsimp at h₁
  have hm₁ : s₁.gpr .x22 = VG.Proof.X25519.AArch64.maskB (sw == 1) := by rw [g₁, hm]
  refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.cswap_inv h₁ (x := 2) (y := 4) (by decide) (by decide) (by decide)
    (k := 18) rfl rfl hm₁) fun s₂ ⟨h₂, _⟩ => ?_)
  vsimp at h₂
  refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.add_inv h₂ (o := 5) (a := 1) (c := 2) (by decide) (by decide) (by decide)
    (ka := 18) (kc := 18) rfl rfl (by decide) (by decide)) fun s₃ h₃ => ?_)
  vsimp at h₃
  refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.mul_inv h₃ (o := 9) (a := 5) (c := 5) (by decide) (by decide) (by decide)
    (ka := 26) (kc := 26) rfl rfl (by decide) (by decide)) fun s₄ h₄ => ?_)
  vsimp at h₄
  refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.sub_inv h₄ (o := 6) (a := 1) (c := 2) (by decide) (by decide) (by decide)
    (ka := 18) (kc := 18) rfl rfl (by decide) (by decide)) fun s₅ h₅ => ?_)
  vsimp at h₅
  refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.mul_inv h₅ (o := 10) (a := 6) (c := 6) (by decide) (by decide) (by decide)
    (ka := 26) (kc := 26) rfl rfl (by decide) (by decide)) fun s₆ h₆ => ?_)
  vsimp at h₆
  refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.sub_inv h₆ (o := 11) (a := 9) (c := 10) (by decide) (by decide) (by decide)
    (ka := 18) (kc := 18) rfl rfl (by decide) (by decide)) fun s₇ h₇ => ?_)
  vsimp at h₇
  refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.add_inv h₇ (o := 7) (a := 3) (c := 4) (by decide) (by decide) (by decide)
    (ka := 18) (kc := 18) rfl rfl (by decide) (by decide)) fun s₈ h₈ => ?_)
  vsimp at h₈
  refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.sub_inv h₈ (o := 8) (a := 3) (c := 4) (by decide) (by decide) (by decide)
    (ka := 18) (kc := 18) rfl rfl (by decide) (by decide)) fun s₉ h₉ => ?_)
  vsimp at h₉
  refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.mul_inv h₉ (o := 12) (a := 8) (c := 5) (by decide) (by decide) (by decide)
    (ka := 26) (kc := 26) rfl rfl (by decide) (by decide)) fun s₁₀ h₁₀ => ?_)
  vsimp at h₁₀
  refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.mul_inv h₁₀ (o := 13) (a := 7) (c := 6) (by decide) (by decide) (by decide)
    (ka := 26) (kc := 26) rfl rfl (by decide) (by decide)) fun s₁₁ h₁₁ => ?_)
  vsimp at h₁₁
  refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.add_inv h₁₁ (o := 3) (a := 12) (c := 13) (by decide) (by decide) (by decide)
    (ka := 18) (kc := 18) rfl rfl (by decide) (by decide)) fun s₁₂ h₁₂ => ?_)
  vsimp at h₁₂
  refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.mul_inv h₁₂ (o := 3) (a := 3) (c := 3) (by decide) (by decide) (by decide)
    (ka := 26) (kc := 26) rfl rfl (by decide) (by decide)) fun s₁₃ h₁₃ => ?_)
  vsimp at h₁₃
  refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.sub_inv h₁₃ (o := 4) (a := 12) (c := 13) (by decide) (by decide) (by decide)
    (ka := 18) (kc := 18) rfl rfl (by decide) (by decide)) fun s₁₄ h₁₄ => ?_)
  vsimp at h₁₄
  refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.mul_inv h₁₄ (o := 4) (a := 4) (c := 4) (by decide) (by decide) (by decide)
    (ka := 26) (kc := 26) rfl rfl (by decide) (by decide)) fun s₁₅ h₁₅ => ?_)
  vsimp at h₁₅
  refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.mul_inv h₁₅ (o := 4) (a := 0) (c := 4) (by decide) (by decide) (by decide)
    (ka := 18) (kc := 18) rfl rfl (by decide) (by decide)) fun s₁₆ h₁₆ => ?_)
  vsimp at h₁₆
  refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.mul_inv h₁₆ (o := 1) (a := 9) (c := 10) (by decide) (by decide) (by decide)
    (ka := 18) (kc := 18) rfl rfl (by decide) (by decide)) fun s₁₇ h₁₇ => ?_)
  vsimp at h₁₇
  refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.mulSmall_inv h₁₇ (o := 2) (a := 11) (by decide) (by decide)
    (ka := 26) rfl (by decide)) fun s₁₈ h₁₈ => ?_)
  vsimp at h₁₈
  refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.add_inv h₁₈ (o := 2) (a := 9) (c := 2) (by decide) (by decide) (by decide)
    (ka := 18) (kc := 18) rfl rfl (by decide) (by decide)) fun s₁₉ h₁₉ => ?_)
  vsimp at h₁₉
  refine WP.mono (VG.Proof.X25519.AArch64.mul_inv h₁₉ (o := 2) (a := 11) (c := 2) (by decide) (by decide) (by decide)
    (ka := 26) (kc := 26) rfl rfl (by decide) (by decide)) fun s₂₀ h₂₀ => ?_
  vsimp at h₂₀
  refine ⟨h₂₀.sc, h₂₀.sl.weaken fun n hn j hj => ?_, h₂₀.kp, h₂₀.fr⟩
  simp only [VG.Proof.X25519.AArch64.lbnds] at hj
  split at hj
  · rename_i h5
    cases hj
    rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4) with rfl | rfl | rfl | rfl | rfl <;>
      refine ⟨rfl, ?_⟩ <;> simp only [Function.update_apply, VG.Proof.X25519.AArch64.lvals, ite_true, ite_false,
        Nat.reduceEqDiff]
  · cases hj

end VG.Proof.X25519.AArch64

namespace VG.Proof.X25519.AArch64

open VG VG.AArch64 VG.Impl.X25519.AArch64 VG.Spec.X25519 VG.Proof.X25519

/-- The registers the ladder writes. -/
abbrev loopRegs : List Reg := VG.Proof.X25519.AArch64.fieldRegs ++ [.x23, .x24]

theorem lvals_congr (x1 : Fe) {st st' : Ladder} (h2 : st.x2 = st'.x2) (hz2 : st.z2 = st'.z2)
    (h3 : st.x3 = st'.x3) (hz3 : st.z3 = st'.z3) : VG.Proof.X25519.AArch64.lvals x1 st = VG.Proof.X25519.AArch64.lvals x1 st' := by
  funext n; simp only [VG.Proof.X25519.AArch64.lvals, h2, hz2, h3, hz3]

/-- A byte of `BITS` is not in the slots. -/
theorem bits_frame {b : Addr} {m m' : Mem} (hf : Frame [VG.Proof.X25519.AArch64.slotArea b] m m') {t : Nat} (ht : t < 256) :
    m' (b + BitVec.ofNat 64 (BITS + t)) = m (b + BitVec.ofNat 64 (BITS + t)) := by
  refine hf _ fun r hr => ?_
  rw [List.mem_singleton.mp hr]
  intro hc
  have := Offset.sep b (d := 64) (n := 1920) (e := BITS + t) (k := 1)
    (by simp only [BITS, slot, NSLOT]; omega) (by decide) (by simp only [BITS, slot, NSLOT]; omega)
  exact this _ hc (by simp only [BitVec.sub_self, BitVec.toNat_zero, Nat.lt_one_iff])

/-- One iteration of the ladder, for the bit `t`. -/
theorem step_ok {b : Addr} {s : State} {k : Nat} {x1 : Fe} {t : Nat} (ht : t < 255)
    (hsc : VG.Proof.X25519.AArch64.Sc b s) (hsl : VG.Proof.X25519.AArch64.Sl s.mem b (VG.Proof.X25519.AArch64.lvals x1 (ladderAfter k x1 (t + 1))) VG.Proof.X25519.AArch64.lbnds)
    (h23 : s.gpr .x23 = BitVec.ofNat 64 (t + 1))
    (h24 : s.gpr .x24 = BitVec.ofNat 64 (ladderAfter k x1 (t + 1)).swap)
    (hbit : s.mem (b + BitVec.ofNat 64 (BITS + t)) = BitVec.ofNat 8 (VG.Proof.X25519.bit k t)) :
    WP isa (.block VG.Impl.X25519.AArch64.step) s fun s' =>
      VG.Proof.X25519.AArch64.Sc b s' ∧ VG.Proof.X25519.AArch64.Sl s'.mem b (VG.Proof.X25519.AArch64.lvals x1 (ladderAfter k x1 t)) VG.Proof.X25519.AArch64.lbnds ∧
      s'.gpr .x23 = BitVec.ofNat 64 t ∧ s'.gpr .x24 = BitVec.ofNat 64 (ladderAfter k x1 t).swap ∧
      VG.Proof.X25519.AArch64.Kp VG.Proof.X25519.AArch64.loopRegs s s' ∧ Frame [VG.Proof.X25519.AArch64.slotArea b] s.mem s'.mem := by
  have hsw := ladderAfter_swap_le k x1 (n := t + 1) (by omega)
  have hkt := bit_le k t
  have e : VG.Impl.X25519.AArch64.step = ([.subImm .x .x23 .x23 1, .add .x .x17 .x3 .x23, .ldrb .x19 .x17 BITS,
      .logic .eor .x .x20 .x24 .x19, .addImm .x .x24 .x19 0] ++ maskOf) ++ (cswap X2 X3 ++ cswap Z2 Z3 ++
      add A X2 Z2 ++ mul AA A A ++ VG.Impl.X25519.AArch64.sub B X2 Z2 ++ mul BB B B ++ VG.Impl.X25519.AArch64.sub E AA BB ++
      add C X3 Z3 ++ VG.Impl.X25519.AArch64.sub D X3 Z3 ++ mul DA D A ++ mul CB C B ++
      add X3 DA CB ++ mul X3 X3 X3 ++ VG.Impl.X25519.AArch64.sub Z3 DA CB ++ mul Z3 Z3 Z3 ++ mul Z3 X1 Z3 ++
      mul X2 AA BB ++ mulSmall Z2 E ++ add Z2 AA Z2 ++ mul Z2 E Z2) := by
    simp only [VG.Impl.X25519.AArch64.step, List.append_assoc]
  rw [e]
  refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.head_ok hsc ht hsw hkt h23 h24 hbit) fun s₁ ⟨e23, e24, e22, k₁, m₁⟩ => ?_)
  have hI : VG.Proof.X25519.AArch64.Inv b s₁ s₁ (VG.Proof.X25519.AArch64.lvals x1 (ladderAfter k x1 (t + 1))) VG.Proof.X25519.AArch64.lbnds :=
    ⟨hsc.of_kp k₁ (by decide), by rw [m₁]; exact hsl, Kp.refl _ _, Frame.refl _ _⟩
  refine WP.mono (VG.Proof.X25519.AArch64.ops_ok hI e22) fun s₂ h₂ => ?_
  have hst := ladderAfter_step k x1 ht
  refine ⟨h₂.sc, ?_, ?_, ?_, (k₁.trans h₂.kp).sub (List.append_subset.mpr ⟨by decide,
    List.subset_append_left _ _⟩), ?_⟩
  · rw [hst, ladderStep_eq]
    exact h₂.sl
  · rw [h₂.kp.gpr _ (by decide), e23]
  · rw [h₂.kp.gpr _ (by decide), e24, hst, ladderStep_eq]
  · rw [← m₁]; exact h₂.fr

/-- The ladder's loop, from the counter `n`: the iterations for the bits `n - 1` down to 0. -/
theorem loop_ok {b : Addr} {s₀ : State} {k : Nat} {x1 : Fe}
    (hbits : ∀ t < 255, s₀.mem (b + BitVec.ofNat 64 (BITS + t)) = BitVec.ofNat 8 (VG.Proof.X25519.bit k t)) :
    ∀ n, ∀ s, (1 ≤ n ∧ n ≤ 255 ∧ VG.Proof.X25519.AArch64.Sc b s ∧ VG.Proof.X25519.AArch64.Sl s.mem b (VG.Proof.X25519.AArch64.lvals x1 (ladderAfter k x1 n)) VG.Proof.X25519.AArch64.lbnds ∧
      s.gpr .x23 = BitVec.ofNat 64 n ∧ s.gpr .x24 = BitVec.ofNat 64 (ladderAfter k x1 n).swap ∧
      VG.Proof.X25519.AArch64.Kp VG.Proof.X25519.AArch64.loopRegs s₀ s ∧ Frame [VG.Proof.X25519.AArch64.slotArea b] s₀.mem s.mem) →
    WP isa (.loop (.block VG.Impl.X25519.AArch64.step) (.nonzero .x .x23)) s fun s' =>
      VG.Proof.X25519.AArch64.Sc b s' ∧ VG.Proof.X25519.AArch64.Sl s'.mem b (VG.Proof.X25519.AArch64.lvals x1 (ladderAfter k x1 0)) VG.Proof.X25519.AArch64.lbnds ∧
      s'.gpr .x24 = BitVec.ofNat 64 (ladderAfter k x1 0).swap ∧ VG.Proof.X25519.AArch64.Kp VG.Proof.X25519.AArch64.loopRegs s₀ s' ∧
      Frame [VG.Proof.X25519.AArch64.slotArea b] s₀.mem s'.mem := by
  refine WP.loop (M := isa) (fun n s => 1 ≤ n ∧ n ≤ 255 ∧ VG.Proof.X25519.AArch64.Sc b s ∧
      VG.Proof.X25519.AArch64.Sl s.mem b (VG.Proof.X25519.AArch64.lvals x1 (ladderAfter k x1 n)) VG.Proof.X25519.AArch64.lbnds ∧
      s.gpr .x23 = BitVec.ofNat 64 n ∧ s.gpr .x24 = BitVec.ofNat 64 (ladderAfter k x1 n).swap ∧
      VG.Proof.X25519.AArch64.Kp VG.Proof.X25519.AArch64.loopRegs s₀ s ∧ Frame [VG.Proof.X25519.AArch64.slotArea b] s₀.mem s.mem) ?_
  rintro n s ⟨h1, h255, hsc, hsl, h23, h24, hkp, hfr⟩
  obtain ⟨t, rfl⟩ : ∃ t, n = t + 1 := ⟨n - 1, by omega⟩
  refine WP.mono (VG.Proof.X25519.AArch64.step_ok (t := t) (by omega) hsc hsl h23 h24
    (by rw [VG.Proof.X25519.AArch64.bits_frame hfr (by omega)]; exact hbits t (by omega))) fun s' ⟨sc', sl', e23, e24, kp', fr'⟩ => ?_
  have hev : isa.eval (.nonzero .x .x23) s' = some (BitVec.ofNat 64 t != 0) := by
    simp only [eval, VG.Proof.X25519.AArch64.read_x, e23]
  have hkp : VG.Proof.X25519.AArch64.Kp VG.Proof.X25519.AArch64.loopRegs s₀ s' := (hkp.trans kp').sub (List.append_subset.mpr
    ⟨List.Subset.refl _, List.Subset.refl _⟩)
  have hfr' : Frame [VG.Proof.X25519.AArch64.slotArea b] s₀.mem s'.mem := hfr.trans fr'
  by_cases ht : t = 0
  · subst ht
    exact .inl ⟨by rw [hev]; rfl, sc', sl', e24, hkp, hfr'⟩
  · refine .inr ⟨?_, t, by omega, by omega, by omega, sc', sl', e23, e24, hkp, hfr'⟩
    rw [hev]
    have : BitVec.ofNat 64 t ≠ 0 := fun h => ht (by
      have := congrArg BitVec.toNat h
      rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this)
    simpa using this

/-- The ladder, from its initial state in the slots. -/
theorem ladder_ok {b : Addr} {s : State} {k : Nat} {x1 : Fe}
    (hsc : VG.Proof.X25519.AArch64.Sc b s) (hsl : VG.Proof.X25519.AArch64.Sl s.mem b (VG.Proof.X25519.AArch64.lvals x1 (init x1)) VG.Proof.X25519.AArch64.lbnds)
    (hbits : ∀ t < 255, s.mem (b + BitVec.ofNat 64 (BITS + t)) = BitVec.ofNat 8 (VG.Proof.X25519.bit k t)) :
    WP isa ladder s fun s' => VG.Proof.X25519.AArch64.Sc b s' ∧ VG.Proof.X25519.AArch64.Sl s'.mem b (VG.Proof.X25519.AArch64.lvals x1 (ladderAfter k x1 0)) VG.Proof.X25519.AArch64.lbnds ∧
      s'.gpr .x24 = BitVec.ofNat 64 (ladderAfter k x1 0).swap ∧ VG.Proof.X25519.AArch64.Kp VG.Proof.X25519.AArch64.loopRegs s s' ∧
      Frame [VG.Proof.X25519.AArch64.slotArea b] s.mem s'.mem := by
  refine WP.seq (WP.mono (Q := fun (s₁ : State) => s₁.gpr .x23 = BitVec.ofNat 64 255 ∧ s₁.gpr .x24 = 0 ∧
    VG.Proof.X25519.AArch64.Kp [.x23, .x24] s s₁ ∧ s₁.mem = s.mem) ?_ fun s₁ ⟨e23, e24, k₁, m₁⟩ => ?_)
  · apply WP.of_runBlock
    simp only [runBlock_cons, VG.Proof.X25519.AArch64.exec_movz, runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left',
      VG.Proof.X25519.AArch64.gpr_wx_self, VG.Proof.X25519.AArch64.gpr_wx_ne _ _ (show Reg.x23 ≠ .x24 by decide)]
    exact ⟨by decide, by decide, ((VG.Proof.X25519.AArch64.kp_wx s _ _).trans (VG.Proof.X25519.AArch64.kp_wx _ _ _)).sub (by sub_regs), rfl⟩
  · refine WP.mono (VG.Proof.X25519.AArch64.loop_ok (s₀ := s) hbits 255 s₁ ⟨by decide, by decide, hsc.of_kp k₁ (by decide),
      by rw [m₁, ladderAfter_255]; exact hsl, e23, by rw [e24, ladderAfter_255]; rfl, k₁.sub (by decide),
      by rw [m₁]; exact Frame.refl _ _⟩) fun s' h => h

end VG.Proof.X25519.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.AArch64.Invert`. -/
section

/-! Kernel-checked ref10 inversion chain, reusing the ladder's dead slots. -/

namespace VG.Proof.X25519.AArch64
open VG VG.AArch64 VG.Impl.X25519.AArch64 VG.Spec.X25519

abbrev invRegs : List Reg := VG.Proof.X25519.AArch64.fieldRegs ++ [.x23]
def IQ : List Nat := [1, 2, 5, 6, 7, 14]
def cbnds (n : Nat) : Option Nat := if n ∈ VG.Proof.X25519.AArch64.IQ then some 18 else none
structure CI (b : Addr) (s₀ s : State) (v : Nat → Fe) : Prop where
  sc : VG.Proof.X25519.AArch64.Sc b s
  sl : VG.Proof.X25519.AArch64.Sl s.mem b v VG.Proof.X25519.AArch64.cbnds
  kp : VG.Proof.X25519.AArch64.Kp VG.Proof.X25519.AArch64.invRegs s₀ s
  fr : Frame [VG.Proof.X25519.AArch64.slotArea b] s₀.mem s.mem

theorem Inv.of_sl {b : Addr} {s : State} {v : Nat → Fe} {bnds : Nat → Option Nat}
    (hs : VG.Proof.X25519.AArch64.Sc b s) (h : VG.Proof.X25519.AArch64.Sl s.mem b v bnds) : VG.Proof.X25519.AArch64.Inv b s s v bnds := ⟨hs, h, Kp.refl _ _, Frame.refl _ _⟩
def cmul (o a c : Nat) (v : Nat → Fe) := Function.update v o (v a * v c)
def ccopy (o a : Nat) (v : Nat → Fe) := Function.update v o (v a)
def csqn (o a n : Nat) (v : Nat → Fe) := Function.update v o (VG.Proof.X25519.sqn (v a) n)
def CS (b : Addr) (c : Prog isa) (f : (Nat → Fe) → Nat → Fe) : Prop :=
  ∀ s₀ s v, VG.Proof.X25519.AArch64.CI b s₀ s v → WP isa c s fun t => VG.Proof.X25519.AArch64.CI b s₀ t (f v)

theorem cbnds_update {o : Nat} (ho : o ∈ VG.Proof.X25519.AArch64.IQ) : Function.update VG.Proof.X25519.AArch64.cbnds o (some 18) = VG.Proof.X25519.AArch64.cbnds := by
  funext n
  by_cases h : n = o
  · subst n; simp [VG.Proof.X25519.AArch64.cbnds, ho]
  · simp [Function.update_of_ne h]
theorem iq_lt {n : Nat} (h : n ∈ VG.Proof.X25519.AArch64.IQ) : n < 15 := by simp only [VG.Proof.X25519.AArch64.IQ, List.mem_cons, List.not_mem_nil, or_false] at h; omega

theorem cmul_ok (b : Addr) (o a c : Nat) (ho : o ∈ VG.Proof.X25519.AArch64.IQ) (ha : a ∈ VG.Proof.X25519.AArch64.IQ) (hc : c ∈ VG.Proof.X25519.AArch64.IQ) :
    VG.Proof.X25519.AArch64.CS b (.block (mul (slot o) (slot a) (slot c))) (VG.Proof.X25519.AArch64.cmul o a c) := by
  intro s₀ s v h
  refine WP.mono (VG.Proof.X25519.AArch64.mul_inv (Inv.of_sl h.sc h.sl) (VG.Proof.X25519.AArch64.iq_lt ho) (VG.Proof.X25519.AArch64.iq_lt ha) (VG.Proof.X25519.AArch64.iq_lt hc)
    (ka := 18) (kc := 18) (by simp [VG.Proof.X25519.AArch64.cbnds, ha]) (by simp [VG.Proof.X25519.AArch64.cbnds, hc]) (by decide) (by decide)) fun t ht => ?_
  exact ⟨ht.sc, by rw [VG.Proof.X25519.AArch64.cbnds_update ho] at ht; exact ht.sl,
    (h.kp.trans ht.kp).sub (List.append_subset.mpr ⟨List.Subset.refl _, List.subset_append_left _ _⟩), h.fr.trans ht.fr⟩
theorem ccopy_ok (b : Addr) (o a : Nat) (ho : o ∈ VG.Proof.X25519.AArch64.IQ) (ha : a ∈ VG.Proof.X25519.AArch64.IQ) :
    VG.Proof.X25519.AArch64.CS b (.block (copy (slot o) (slot a))) (VG.Proof.X25519.AArch64.ccopy o a) := by
  intro s₀ s v h
  refine WP.mono (VG.Proof.X25519.AArch64.copy_inv (Inv.of_sl h.sc h.sl) (VG.Proof.X25519.AArch64.iq_lt ho) (VG.Proof.X25519.AArch64.iq_lt ha)
    (ka := 18) (by simp [VG.Proof.X25519.AArch64.cbnds, ha])) fun t ht => ?_
  exact ⟨ht.sc, by rw [VG.Proof.X25519.AArch64.cbnds_update ho] at ht; exact ht.sl,
    (h.kp.trans ht.kp).sub (List.append_subset.mpr ⟨List.Subset.refl _, List.subset_append_left _ _⟩), h.fr.trans ht.fr⟩
theorem CS.seq {b : Addr} {p q : Prog isa} {f g} (hp : VG.Proof.X25519.AArch64.CS b p f) (hq : VG.Proof.X25519.AArch64.CS b q g) :
    VG.Proof.X25519.AArch64.CS b (.seq p q) (fun v => g (f v)) := by
  intro s₀ s v h
  exact WP.seq (WP.mono (hp s₀ s v h) fun t ht => hq s₀ t (f v) ht)
theorem CS.append {b : Addr} {p q : List Instr} {f g} (hp : VG.Proof.X25519.AArch64.CS b (.block p) f) (hq : VG.Proof.X25519.AArch64.CS b (.block q) g) :
    VG.Proof.X25519.AArch64.CS b (.block (p ++ q)) (fun v => g (f v)) := by
  intro s₀ s v h
  exact WP.block_append (WP.mono (hp s₀ s v h) fun t ht => hq s₀ t (f v) ht)

theorem counter_ok {b : Addr} {s₀ s : State} {v : Nat → Fe} (h : VG.Proof.X25519.AArch64.CI b s₀ s v) (n : Nat) (hn : n < 65536) :
    WP isa (.block [.movz .x .x23 n 0]) s fun t => VG.Proof.X25519.AArch64.CI b s₀ t v ∧ t.gpr .x23 = BitVec.ofNat 64 n := by
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.X25519.AArch64.exec_movz, WP.block_nil ?_⟩
  exact ⟨⟨VG.Proof.X25519.AArch64.sc_wx _ _ h.sc (by decide), h.sl,
    (h.kp.trans (VG.Proof.X25519.AArch64.kp_wx _ _ _)).sub (List.append_subset.mpr ⟨List.Subset.refl _, by simp [VG.Proof.X25519.AArch64.invRegs]⟩), h.fr⟩,
    by rw [VG.Proof.X25519.AArch64.gpr_wx_self]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]⟩
theorem dec_ok {b : Addr} {s₀ s : State} {v : Nat → Fe} {n : Nat} (h : VG.Proof.X25519.AArch64.CI b s₀ s v)
    (he : s.gpr .x23 = BitVec.ofNat 64 (n + 1)) (_hn : n < 65536) :
    WP isa (.block [.subImm .x .x23 .x23 1]) s fun t => VG.Proof.X25519.AArch64.CI b s₀ t v ∧ t.gpr .x23 = BitVec.ofNat 64 n := by
  refine WP.block_cons_iff.mpr ⟨_, exec_subImm_x (d := .x23) (n := .x23) (imm := 1) (by decide), WP.block_nil ?_⟩
  exact ⟨⟨VG.Proof.X25519.AArch64.sc_wx _ _ h.sc (by decide), h.sl,
    (h.kp.trans (VG.Proof.X25519.AArch64.kp_wx _ _ _)).sub (List.append_subset.mpr ⟨List.Subset.refl _, by simp [VG.Proof.X25519.AArch64.invRegs]⟩), h.fr⟩,
    by rw [VG.Proof.X25519.AArch64.gpr_wx_self, VG.Proof.X25519.AArch64.read_x, he, BitVec.ofNat_add, BitVec.add_sub_cancel]⟩

theorem csqn_ok (b : Addr) (o a n : Nat) (ho : o ∈ VG.Proof.X25519.AArch64.IQ) (ha : a ∈ VG.Proof.X25519.AArch64.IQ) (hn : 1 ≤ n) (hn' : n < 65536) :
    VG.Proof.X25519.AArch64.CS b (Impl.X25519.AArch64.sqn (slot o) (slot a) n) (VG.Proof.X25519.AArch64.csqn o a n) := by
  intro s₀ s v h
  refine WP.seq (WP.block_append (WP.mono (VG.Proof.X25519.AArch64.ccopy_ok b o a ho ha s₀ s v h) fun t ht =>
    WP.mono (VG.Proof.X25519.AArch64.counter_ok ht n hn') fun u ⟨hu, eu⟩ => ?_))
  refine WP.loop (M := isa) (fun k t => 1 ≤ k ∧ k ≤ n ∧
    VG.Proof.X25519.AArch64.CI b s₀ t (Function.update v o (VG.Proof.X25519.sqn (v a) (n-k))) ∧
    t.gpr .x23 = BitVec.ofNat 64 k) ?_ n u ⟨hn, Nat.le_refl _, by simpa [VG.Proof.X25519.AArch64.ccopy, VG.Proof.X25519.sqn] using hu, eu⟩
  intro k t ⟨hk, hkn, ht, et⟩
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k-1, by omega⟩
  refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.mul_inv (Inv.of_sl ht.sc ht.sl) (VG.Proof.X25519.AArch64.iq_lt ho) (VG.Proof.X25519.AArch64.iq_lt ho) (VG.Proof.X25519.AArch64.iq_lt ho)
    (ka := 18) (kc := 18) (by simp [VG.Proof.X25519.AArch64.cbnds, ho]) (by simp [VG.Proof.X25519.AArch64.cbnds, ho]) (by decide) (by decide)) fun u hu => ?_)
  have eu : u.gpr .x23 = BitVec.ofNat 64 (k+1) := by rw [hu.kp.gpr _ (by decide), et]
  have hi : VG.Proof.X25519.AArch64.CI b s₀ u (Function.update v o (VG.Proof.X25519.sqn (v a) (n-k))) := by
    refine ⟨hu.sc, ?_, (ht.kp.trans hu.kp).sub (List.append_subset.mpr
      ⟨List.Subset.refl _, List.subset_append_left _ _⟩), ht.fr.trans hu.fr⟩
    rw [VG.Proof.X25519.AArch64.cbnds_update ho] at hu
    have he : Function.update (Function.update v o (VG.Proof.X25519.sqn (v a) (n-(k+1)))) o
        ((Function.update v o (VG.Proof.X25519.sqn (v a) (n-(k+1)))) o *
         (Function.update v o (VG.Proof.X25519.sqn (v a) (n-(k+1)))) o) =
        Function.update v o (VG.Proof.X25519.sqn (v a) (n-k)) := by
      rw [Function.update_self, Function.update_idem, show n-k = n-(k+1)+1 by omega]
      rfl
    rw [he] at hu
    exact hu.sl
  refine WP.mono (VG.Proof.X25519.AArch64.dec_ok hi eu (by omega)) fun t ⟨ht, et⟩ => ?_
  have hev : isa.eval (.nonzero .x .x23) t = some (BitVec.ofNat 64 k != 0) := by simp [eval, VG.Proof.X25519.AArch64.read_x, et]
  by_cases hk0 : k = 0
  · subst k
    exact .inl ⟨by rw [hev]; rfl, by simpa [VG.Proof.X25519.AArch64.csqn] using ht⟩
  · refine .inr ⟨?_, k, by omega, by omega, by omega, ht, et⟩
    rw [hev]
    apply congrArg some
    apply bne_iff_ne.mpr
    intro he
    have := congrArg BitVec.toNat he
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : k < 2^64)] at this
    exact hk0 this

def chainEnv (v : Nat → Fe) : Nat → Fe := VG.Proof.X25519.AArch64.cmul 14 14 5 (VG.Proof.X25519.AArch64.csqn 14 14 5 (VG.Proof.X25519.AArch64.cmul 14 6 14 (VG.Proof.X25519.AArch64.csqn 6 6 50 (VG.Proof.X25519.AArch64.cmul 6 7 6 (VG.Proof.X25519.AArch64.csqn 7 6 100 (VG.Proof.X25519.AArch64.cmul 6 6 14 (VG.Proof.X25519.AArch64.csqn 6 14 50 (VG.Proof.X25519.AArch64.cmul 14 6 14 (VG.Proof.X25519.AArch64.csqn 6 6 10 (VG.Proof.X25519.AArch64.cmul 6 7 6 (VG.Proof.X25519.AArch64.csqn 7 6 20 (VG.Proof.X25519.AArch64.cmul 6 6 14 (VG.Proof.X25519.AArch64.csqn 6 14 10 (VG.Proof.X25519.AArch64.cmul 14 6 14 (VG.Proof.X25519.AArch64.csqn 6 14 5 (VG.Proof.X25519.AArch64.cmul 14 14 6 (VG.Proof.X25519.AArch64.cmul 6 5 5 (VG.Proof.X25519.AArch64.cmul 5 5 14 (VG.Proof.X25519.AArch64.cmul 14 2 14 (VG.Proof.X25519.AArch64.csqn 14 5 2 (VG.Proof.X25519.AArch64.cmul 5 2 2 (v))))))))))))))))))))))

theorem chain_spec (b : Addr) : VG.Proof.X25519.AArch64.CS b invChain VG.Proof.X25519.AArch64.chainEnv := by
  have h : VG.Proof.X25519.AArch64.CS b _ _ := (CS.seq (VG.Proof.X25519.AArch64.cmul_ok b 5 2 2 (by decide) (by decide) (by decide))
    (CS.seq (VG.Proof.X25519.AArch64.csqn_ok b 14 5 2 (by decide) (by decide) (by decide) (by decide))
    (CS.seq (CS.append (CS.append (CS.append (VG.Proof.X25519.AArch64.cmul_ok b 14 2 14 (by decide) (by decide) (by decide)) (VG.Proof.X25519.AArch64.cmul_ok b 5 5 14 (by decide) (by decide) (by decide))) (VG.Proof.X25519.AArch64.cmul_ok b 6 5 5 (by decide) (by decide) (by decide))) (VG.Proof.X25519.AArch64.cmul_ok b 14 14 6 (by decide) (by decide) (by decide)))
    (CS.seq (VG.Proof.X25519.AArch64.csqn_ok b 6 14 5 (by decide) (by decide) (by decide) (by decide))
    (CS.seq (VG.Proof.X25519.AArch64.cmul_ok b 14 6 14 (by decide) (by decide) (by decide))
    (CS.seq (VG.Proof.X25519.AArch64.csqn_ok b 6 14 10 (by decide) (by decide) (by decide) (by decide))
    (CS.seq (VG.Proof.X25519.AArch64.cmul_ok b 6 6 14 (by decide) (by decide) (by decide))
    (CS.seq (VG.Proof.X25519.AArch64.csqn_ok b 7 6 20 (by decide) (by decide) (by decide) (by decide))
    (CS.seq (VG.Proof.X25519.AArch64.cmul_ok b 6 7 6 (by decide) (by decide) (by decide))
    (CS.seq (VG.Proof.X25519.AArch64.csqn_ok b 6 6 10 (by decide) (by decide) (by decide) (by decide))
    (CS.seq (VG.Proof.X25519.AArch64.cmul_ok b 14 6 14 (by decide) (by decide) (by decide))
    (CS.seq (VG.Proof.X25519.AArch64.csqn_ok b 6 14 50 (by decide) (by decide) (by decide) (by decide))
    (CS.seq (VG.Proof.X25519.AArch64.cmul_ok b 6 6 14 (by decide) (by decide) (by decide))
    (CS.seq (VG.Proof.X25519.AArch64.csqn_ok b 7 6 100 (by decide) (by decide) (by decide) (by decide))
    (CS.seq (VG.Proof.X25519.AArch64.cmul_ok b 6 7 6 (by decide) (by decide) (by decide))
    (CS.seq (VG.Proof.X25519.AArch64.csqn_ok b 6 6 50 (by decide) (by decide) (by decide) (by decide))
    (CS.seq (VG.Proof.X25519.AArch64.cmul_ok b 14 6 14 (by decide) (by decide) (by decide))
    (CS.seq (VG.Proof.X25519.AArch64.csqn_ok b 14 14 5 (by decide) (by decide) (by decide) (by decide))
    (VG.Proof.X25519.AArch64.cmul_ok b 14 14 5 (by decide) (by decide) (by decide))))))))))))))))))))
  exact h

theorem chain_eval (v : Nat → Fe) : VG.Proof.X25519.AArch64.chainEnv v 14 = VG.Proof.X25519.invert (v 2) := by
  simp only [↓reduceIte, Nat.reduceEqDiff, VG.Proof.X25519.AArch64.chainEnv, VG.Proof.X25519.AArch64.cmul, VG.Proof.X25519.AArch64.csqn, Function.update_apply]
  rfl

theorem chain_keep (v : Nat → Fe) : VG.Proof.X25519.AArch64.chainEnv v 1 = v 1 := by
  simp only [↓reduceIte, Nat.reduceEqDiff, VG.Proof.X25519.AArch64.chainEnv, VG.Proof.X25519.AArch64.cmul, VG.Proof.X25519.AArch64.csqn, Function.update_apply]

def fbnds (n : Nat) : Option Nat := if n = 1 ∨ n = 14 then some 18 else none

theorem invert_ok {b : Addr} {s : State} {v : Nat → Fe} {bnds : Nat → Option Nat} {z : Fe}
    (hs : VG.Proof.X25519.AArch64.Sc b s) (hsl : VG.Proof.X25519.AArch64.Sl s.mem b v bnds) (hz : v 2 = z)
    (hb2 : bnds 2 = some 18) (hb1 : bnds 1 = some 18) :
    WP isa Impl.X25519.AArch64.invert s fun t => VG.Proof.X25519.AArch64.Sc b t ∧
      VG.Proof.X25519.AArch64.Sl t.mem b (Function.update v 14 (pow z (P-2))) VG.Proof.X25519.AArch64.fbnds ∧
      VG.Proof.X25519.AArch64.Kp VG.Proof.X25519.AArch64.invRegs s t ∧ Frame [VG.Proof.X25519.AArch64.slotArea b] s.mem t.mem := by
  unfold Impl.X25519.AArch64.invert
  simp only [List.append_assoc]
  refine WP.seq (WP.block_append (WP.mono (VG.Proof.X25519.AArch64.copy_inv (Inv.of_sl hs hsl)
    (o := 5) (a := 2) (by decide) (by decide) hb2) fun t₁ h₁ => ?_))
  refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.copy_inv h₁ (o := 6) (a := 2) (by decide) (by decide)
    (ka := 18) (by simp [hb2])) fun t₂ h₂ => ?_)
  refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.copy_inv h₂ (o := 7) (a := 2) (by decide) (by decide)
    (ka := 18) (by simp [hb2])) fun t₃ h₃ => ?_)
  refine WP.mono (VG.Proof.X25519.AArch64.copy_inv h₃ (o := 14) (a := 2) (by decide) (by decide)
    (ka := 18) (by simp [hb2])) fun t₄ h₄ => ?_
  have hi : VG.Proof.X25519.AArch64.CI b s t₄ (VG.Proof.X25519.AArch64.ccopy 14 2 (VG.Proof.X25519.AArch64.ccopy 7 2 (VG.Proof.X25519.AArch64.ccopy 6 2 (VG.Proof.X25519.AArch64.ccopy 5 2 v)))) := ⟨h₄.sc, h₄.sl.weaken (fun n hn k hk => by
    simp only [VG.Proof.X25519.AArch64.cbnds] at hk
    split at hk
    · cases hk
      rename_i hq
      simp only [VG.Proof.X25519.AArch64.IQ, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp [hb1, hb2], rfl⟩
    · cases hk), h₄.kp.sub (List.subset_append_left _ _), h₄.fr⟩
  refine WP.mono (VG.Proof.X25519.AArch64.chain_spec b s t₄ _ hi) fun t ht => ⟨ht.sc, ?_, ht.kp, ht.fr⟩
  intro n hn k hk
  simp only [VG.Proof.X25519.AArch64.fbnds] at hk
  split at hk
  · cases hk
    rename_i hq
    rcases hq with rfl | rfl
    · have h := ht.sl 1 (by decide) 18 (by decide)
      simpa [VG.Proof.X25519.AArch64.chain_keep, VG.Proof.X25519.AArch64.ccopy, Function.update_of_ne] using h
    · have h := ht.sl 14 (by decide) 18 (by decide)
      simpa [VG.Proof.X25519.AArch64.chain_eval, VG.Proof.X25519.AArch64.ccopy, VG.Proof.X25519.invert_eq, hz] using h
  · cases hk

end VG.Proof.X25519.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.AArch64.Final`. -/
section

/-!
# X25519 on AArch64: the full reduction and the result

`finish`: the product `x2 · z2^(p-2)`, loaded into the limb registers, reduced
fully (`freeze`), packed into four words at `out` (`pack`), and our caller's
registers restored.
-/

namespace VG.Proof.X25519.AArch64

open VG VG.AArch64 VG.Impl.X25519.AArch64 VG.Spec.X25519 VG.Proof.X25519

/-! ## Loading the limbs -/

theorem loads_ok {b : Addr} {a : Nat} (ha : VG.Proof.X25519.AArch64.Slot a) :
    ∀ n ≤ 15, ∀ s : State, VG.Proof.X25519.AArch64.Sc b s →
    WP isa (.block ((List.range n).map fun k => ld (dreg k) (a + 8 * k))) s fun s' =>
      (∀ k < n, VG.Proof.X25519.AArch64.v s' (dreg k) = VG.Proof.X25519.AArch64.wd s.mem b (a + 8 * k)) ∧ VG.Proof.X25519.AArch64.Kp DR s s' ∧ s'.mem = s.mem
  | 0, _, s, _ => WP.block_nil ⟨fun k hk => absurd hk (Nat.not_lt_zero _), Kp.refl _ _, rfl⟩
  | n + 1, hn, s, hs => by
    rw [List.range_succ, List.map_append, List.map_singleton]
    refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.loads_ok ha n (by omega) s hs) fun s₁ ⟨e₁, k₁, m₁⟩ => ?_)
    have hs₁ := hs.of_kp k₁ (by decide)
    refine WP.block_cons_iff.mpr ⟨_, VG.Proof.X25519.AArch64.exec_ld hs₁ _ (ha.off (i := n) (by omega)), WP.block_nil
      ⟨fun k hk => ?_, (k₁.trans (VG.Proof.X25519.AArch64.kp_wx _ _ _)).sub (List.append_subset.mpr ⟨List.Subset.refl _, by
        simp only [List.cons_subset, List.nil_subset, and_true]; exact VG.Proof.X25519.AArch64.dreg_mem n (by omega)⟩), by
        rw [VG.Proof.X25519.AArch64.mem_wx, m₁]⟩⟩
    by_cases hkn : k = n
    · subst hkn; rw [VG.Proof.X25519.AArch64.v, VG.Proof.X25519.AArch64.gpr_wx_self, VG.Proof.X25519.AArch64.wd_def, m₁]
    · rw [VG.Proof.X25519.AArch64.v, VG.Proof.X25519.AArch64.gpr_wx_ne _ _ (VG.Proof.X25519.AArch64.dreg_ne (by omega) (by omega) hkn)]; exact e₁ k (by omega)

theorem load_ok {b : Addr} {s : State} (hs : VG.Proof.X25519.AArch64.Sc b s) {a : Nat} (ha : VG.Proof.X25519.AArch64.Slot a) :
    WP isa (.block (load a)) s fun s' => VG.Proof.X25519.AArch64.regs s' = VG.Proof.X25519.AArch64.limbs s.mem b a ∧ VG.Proof.X25519.AArch64.Kp DR s s' ∧ s'.mem = s.mem :=
  WP.mono (VG.Proof.X25519.AArch64.loads_ok ha 15 (by decide) s hs) fun s' ⟨e, k, m⟩ => ⟨funext fun i => by
    simp only [VG.Proof.X25519.AArch64.regs, VG.Proof.X25519.AArch64.limbs]; split
    · rename_i hi; exact e i hi
    · rfl, k, m⟩

/-! ## The full reduction -/

theorem quotN_ok : ∀ n ≤ 14, ∀ s : State,
    WP isa (.block (([.addImm .x .x17 (dreg 0) 19, .lsr .x .x17 .x17 17] : List Instr) ++
      (List.range n).flatMap fun k => [.add .x .x17 (dreg (k + 1)) .x17, .lsr .x .x17 .x17 17])) s
      fun s' => VG.Proof.X25519.AArch64.v s' .x17 = VG.Proof.X25519.AArch64.quotN (VG.Proof.X25519.AArch64.regs s) n ∧ VG.Proof.X25519.AArch64.Kp [.x17] s s' ∧ s'.mem = s.mem
  | 0, _, s => by
    apply WP.of_runBlock
    simp only [List.range_zero, List.flatMap_nil, List.append_nil, runBlock_cons,
      exec_addImm_x (show 19 < 4096 by decide), runStep_some, VG.Proof.X25519.AArch64.exec_lsr (show 17 < 64 by decide), VG.Proof.X25519.AArch64.read_x,
      VG.Proof.X25519.AArch64.gpr_wx_self, runBlock_nil, Option.some.injEq, exists_eq_left']
    refine ⟨?_, ((VG.Proof.X25519.AArch64.kp_wx s _ _).trans (VG.Proof.X25519.AArch64.kp_wx _ _ _)).sub (by sub_regs), rfl⟩
    rw [VG.Proof.X25519.AArch64.v, VG.Proof.X25519.AArch64.gpr_wx_self, VG.Proof.X25519.AArch64.lsr_toNat, BitVec.toNat_add, VG.Proof.X25519.AArch64.quotN, VG.Proof.X25519.AArch64.regs, ite_eq_left (by decide)]; rfl
  | n + 1, hn, s => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, ← List.append_assoc]
    refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.quotN_ok n (by omega) s) fun s₁ ⟨e₁, k₁, m₁⟩ => ?_)
    obtain ⟨d17, -⟩ := VG.Proof.X25519.AArch64.dreg_facts (n + 1) (by omega)
    apply WP.of_runBlock
    simp only [runBlock_cons, VG.Proof.X25519.AArch64.exec_add_x, runStep_some, VG.Proof.X25519.AArch64.exec_lsr (show 17 < 64 by decide),
      VG.Proof.X25519.AArch64.gpr_wx_self, runBlock_nil, Option.some.injEq, exists_eq_left']
    refine ⟨?_, ((k₁.trans (VG.Proof.X25519.AArch64.kp_wx _ _ _)).trans (VG.Proof.X25519.AArch64.kp_wx _ _ _)).sub (by sub_regs), by rw [VG.Proof.X25519.AArch64.mem_wx, VG.Proof.X25519.AArch64.mem_wx, m₁]⟩
    rw [VG.Proof.X25519.AArch64.v, VG.Proof.X25519.AArch64.gpr_wx_self, VG.Proof.X25519.AArch64.lsr_toNat, BitVec.toNat_add, VG.Proof.X25519.AArch64.quotN, show (s₁.gpr .x17).toNat = _ from e₁,
      show (s₁.gpr (dreg (n + 1))).toNat = VG.Proof.X25519.AArch64.regs s (n + 1) by
        rw [VG.Proof.X25519.AArch64.regs, ite_eq_left (by omega), VG.Proof.X25519.AArch64.v, k₁.gpr _ (by simpa using d17)]]

theorem add19_ok {s : State} (h19 : s.gpr .x21 = 19) :
    WP isa (.block [.madd .x (dreg 0) .x17 .x21 (dreg 0)]) s fun s' =>
      VG.Proof.X25519.AArch64.regs s' = VG.Proof.X25519.AArch64.add19 (VG.Proof.X25519.AArch64.regs s) (VG.Proof.X25519.AArch64.v s .x17) ∧ VG.Proof.X25519.AArch64.Kp DR s s' ∧ s'.mem = s.mem := by
  obtain ⟨d17, -, -, d21, -⟩ := VG.Proof.X25519.AArch64.dreg_facts 0 (by decide)
  apply WP.of_runBlock
  simp only [runBlock_cons, VG.Proof.X25519.AArch64.exec_madd_x, runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left']
  refine ⟨funext fun i => ?_, (VG.Proof.X25519.AArch64.kp_wx s _ _).sub (by
    simp only [List.cons_subset, List.nil_subset, and_true]; exact VG.Proof.X25519.AArch64.dreg_mem 0 (by decide)), rfl⟩
  simp only [VG.Proof.X25519.AArch64.regs, VG.Proof.X25519.AArch64.add19]
  by_cases hi : i < 15
  · simp only [hi, ite_true]
    by_cases h0 : i = 0
    · subst h0
      rw [ite_eq_left rfl, VG.Proof.X25519.AArch64.v, VG.Proof.X25519.AArch64.gpr_wx_self, VG.Proof.X25519.AArch64.madd_toNat, h19, ite_eq_left (by decide)]; rfl
    · rw [ite_eq_right h0, VG.Proof.X25519.AArch64.v, VG.Proof.X25519.AArch64.gpr_wx_ne _ _ (VG.Proof.X25519.AArch64.dreg_ne hi (by decide) h0)]
  · simp only [hi, ite_false, show i ≠ 0 by omega]

theorem maskTop_ok {s : State} (hm : s.gpr .x22 = 0x1ffff) :
    WP isa (.block [.logic .and .x (dreg 14) (dreg 14) .x22]) s fun s' =>
      VG.Proof.X25519.AArch64.regs s' = VG.Proof.X25519.AArch64.maskTop (VG.Proof.X25519.AArch64.regs s) ∧ VG.Proof.X25519.AArch64.Kp DR s s' ∧ s'.mem = s.mem := by
  apply WP.of_runBlock
  simp only [runBlock_cons, VG.Proof.X25519.AArch64.exec_and_x, runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left']
  refine ⟨funext fun i => ?_, (VG.Proof.X25519.AArch64.kp_wx s _ _).sub (by
    simp only [List.cons_subset, List.nil_subset, and_true]; exact VG.Proof.X25519.AArch64.dreg_mem 14 (by decide)), rfl⟩
  simp only [VG.Proof.X25519.AArch64.regs, VG.Proof.X25519.AArch64.maskTop]
  by_cases hi : i < 15
  · simp only [hi, ite_true]
    by_cases h14 : i = 14
    · subst h14
      rw [ite_eq_left rfl, VG.Proof.X25519.AArch64.v, VG.Proof.X25519.AArch64.gpr_wx_self, VG.Proof.X25519.AArch64.and_mask17 _ _ hm, ite_eq_left (by decide)]
    · rw [ite_eq_right h14, VG.Proof.X25519.AArch64.v, VG.Proof.X25519.AArch64.gpr_wx_ne _ _ (VG.Proof.X25519.AArch64.dreg_ne hi (by decide) h14)]
  · simp only [hi, ite_false, show i ≠ 14 by omega]

theorem kp_field {W : List Reg} {s s' : State} (h : VG.Proof.X25519.AArch64.Kp W s s') (hW : W ⊆ VG.Proof.X25519.AArch64.fieldRegs) : VG.Proof.X25519.AArch64.Kp VG.Proof.X25519.AArch64.fieldRegs s s' :=
  h.sub hW

theorem DR_sub : DR ⊆ VG.Proof.X25519.AArch64.fieldRegs := fun _ h => List.mem_append_left _ (List.mem_append_left _ h)

/-- `freeze`: the limb registers reduced fully. -/
theorem freeze_ok (s : State) :
    WP isa (.block freeze) s fun s' => VG.Proof.X25519.AArch64.regs s' = VG.Proof.X25519.AArch64.freezeF (VG.Proof.X25519.AArch64.regs s) ∧ VG.Proof.X25519.AArch64.Kp VG.Proof.X25519.AArch64.fieldRegs s s' ∧ s'.mem = s.mem := by
  simp only [freeze, List.append_assoc]
  refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.mask17_ok s) fun s₁ ⟨e₁, k₁, m₁⟩ => ?_)
  refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.const19_ok s₁) fun s₂ ⟨e₂, k₂, m₂⟩ => ?_)
  have hm₂ : s₂.gpr .x22 = 0x1ffff := by rw [k₂.gpr _ (by decide), e₁]
  have r₂ : VG.Proof.X25519.AArch64.regs s₂ = VG.Proof.X25519.AArch64.regs s := funext fun i => by
    simp only [VG.Proof.X25519.AArch64.regs]; split
    · rename_i hi
      obtain ⟨-, -, -, d21, d22, -⟩ := VG.Proof.X25519.AArch64.dreg_facts i hi
      rw [VG.Proof.X25519.AArch64.v, k₂.gpr _ (by simpa using d21), k₁.gpr _ (by simpa using d22)]
    · rfl
  refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.chain_ok 14 (by decide) s₂ hm₂) fun s₃ ⟨e₃, k₃, m₃⟩ => ?_)
  have hm₃ : s₃.gpr .x22 = 0x1ffff := by rw [k₃.gpr _ (by decide), hm₂]
  have h19₃ : s₃.gpr .x21 = 19 := by rw [k₃.gpr _ (by decide), e₂]
  refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.foldTop_ok hm₃ h19₃) fun s₄ ⟨e₄, k₄, m₄⟩ => ?_)
  have hm₄ : s₄.gpr .x22 = 0x1ffff := by rw [k₄.gpr _ (by decide), hm₃]
  have h19₄ : s₄.gpr .x21 = 19 := by rw [k₄.gpr _ (by decide), h19₃]
  refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.chain_ok 14 (by decide) s₄ hm₄) fun s₅ ⟨e₅, k₅, m₅⟩ => ?_)
  have hm₅ : s₅.gpr .x22 = 0x1ffff := by rw [k₅.gpr _ (by decide), hm₄]
  have h19₅ : s₅.gpr .x21 = 19 := by rw [k₅.gpr _ (by decide), h19₄]
  refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.foldTop_ok hm₅ h19₅) fun s₆ ⟨e₆, k₆, m₆⟩ => ?_)
  have hm₆ : s₆.gpr .x22 = 0x1ffff := by rw [k₆.gpr _ (by decide), hm₅]
  have h19₆ : s₆.gpr .x21 = 19 := by rw [k₆.gpr _ (by decide), h19₅]
  refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.quotN_ok 14 (by decide) s₆ : WP isa (.block quot) s₆ _)
    fun s₇ ⟨e₇, k₇, m₇⟩ => ?_)
  have hm₇ : s₇.gpr .x22 = 0x1ffff := by rw [k₇.gpr _ (by decide), hm₆]
  have h19₇ : s₇.gpr .x21 = 19 := by rw [k₇.gpr _ (by decide), h19₆]
  have r₇ : VG.Proof.X25519.AArch64.regs s₇ = VG.Proof.X25519.AArch64.regs s₆ := funext fun i => by
    simp only [VG.Proof.X25519.AArch64.regs]; split
    · rename_i hi
      obtain ⟨d17, -⟩ := VG.Proof.X25519.AArch64.dreg_facts i hi
      rw [VG.Proof.X25519.AArch64.v, k₇.gpr _ (by simpa using d17)]
    · rfl
  refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.add19_ok h19₇) fun s₈ ⟨e₈, k₈, m₈⟩ => ?_)
  have hm₈ : s₈.gpr .x22 = 0x1ffff := by rw [k₈.gpr _ (by decide), hm₇]
  refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.chain_ok 14 (by decide) s₈ hm₈) fun s₉ ⟨e₉, k₉, m₉⟩ => ?_)
  have hm₉ : s₉.gpr .x22 = 0x1ffff := by rw [k₉.gpr _ (by decide), hm₈]
  refine WP.mono (VG.Proof.X25519.AArch64.maskTop_ok hm₉) fun s₁₀ ⟨e₁₀, k₁₀, m₁₀⟩ => ⟨?_, ?_, ?_⟩
  · rw [e₁₀, e₉, e₈, e₇, r₇, e₆, e₅, e₄, e₃, r₂]; rfl
  · exact (((((((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans k₆).trans k₇).trans k₈).trans
      k₉).trans k₁₀).sub (by decide)
  · rw [m₁₀, m₉, m₈, m₇, m₆, m₅, m₄, m₃, m₂, m₁]

/-! ## Packing -/

theorem regs_kp {s s' : State} {W : List Reg} (h : VG.Proof.X25519.AArch64.Kp W s s') (hW : ∀ k < 15, dreg k ∉ W) : VG.Proof.X25519.AArch64.regs s' = VG.Proof.X25519.AArch64.regs s :=
  funext fun i => by
    simp only [VG.Proof.X25519.AArch64.regs]; split
    · rename_i hi; rw [VG.Proof.X25519.AArch64.v, h.gpr _ (hW i hi)]
    · rfl

theorem place_ok {s : State} {t : Reg} {i j : Nat} (hi : i < 15) (hw : 64 * j < 17 * i + 17 ∧ 17 * i < 64 * j + 64) :
    WP isa (.block [place t i j]) s fun s' => VG.Proof.X25519.AArch64.v s' t = VG.Proof.X25519.AArch64.placeV (VG.Proof.X25519.AArch64.regs s) i j ∧ VG.Proof.X25519.AArch64.Kp [t] s s' ∧ s'.mem = s.mem := by
  apply WP.of_runBlock
  simp only [place, VG.Proof.X25519.AArch64.placeV, VG.Proof.X25519.AArch64.regs, hi, ite_true]
  split
  · simp only [runBlock_cons, VG.Proof.X25519.AArch64.exec_lsl (show 17 * i - 64 * j < 64 by omega), runStep_some, runBlock_nil,
      Option.some.injEq, exists_eq_left', VG.Proof.X25519.AArch64.v, VG.Proof.X25519.AArch64.gpr_wx_self, VG.Proof.X25519.AArch64.lsl_toNat]
    exact ⟨trivial, VG.Proof.X25519.AArch64.kp_wx s _ _, rfl⟩
  · simp only [runBlock_cons, VG.Proof.X25519.AArch64.exec_lsr (show 64 * j - 17 * i < 64 by omega), runStep_some, runBlock_nil,
      Option.some.injEq, exists_eq_left', VG.Proof.X25519.AArch64.v, VG.Proof.X25519.AArch64.gpr_wx_self, VG.Proof.X25519.AArch64.lsr_toNat]
    exact ⟨trivial, VG.Proof.X25519.AArch64.kp_wx s _ _, rfl⟩

theorem accs_ok {j : Nat} : ∀ (is : List Nat), (∀ i ∈ is, i < 15 ∧ 64 * j < 17 * i + 17 ∧ 17 * i < 64 * j + 64) →
    ∀ s : State, WP isa (.block (is.flatMap fun i => [place .x19 i j, .add .x .x17 .x17 .x19])) s fun s' =>
      VG.Proof.X25519.AArch64.v s' .x17 = is.foldl (fun acc i => (acc + VG.Proof.X25519.AArch64.placeV (VG.Proof.X25519.AArch64.regs s) i j) % 2 ^ 64) (VG.Proof.X25519.AArch64.v s .x17) ∧
      VG.Proof.X25519.AArch64.Kp [.x17, .x19] s s' ∧ s'.mem = s.mem
  | [], _, s => WP.block_nil ⟨rfl, Kp.refl _ _, rfl⟩
  | i :: is, h, s => by
    obtain ⟨hi, hw⟩ := h i List.mem_cons_self
    rw [List.flatMap_cons, show [place .x19 i j, .add .x .x17 .x17 .x19] =
      [place .x19 i j] ++ ([.add .x .x17 .x17 .x19] : List Instr) from rfl, List.append_assoc]
    refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.place_ok (t := .x19) hi hw) fun s₁ ⟨e₁, k₁, m₁⟩ => ?_)
    refine WP.block_cons_iff.mpr ⟨_, VG.Proof.X25519.AArch64.exec_add_x, ?_⟩
    have r₂ : VG.Proof.X25519.AArch64.regs (s₁.write .x .x17 (s₁.gpr .x17 + s₁.gpr .x19)) = VG.Proof.X25519.AArch64.regs s :=
      (VG.Proof.X25519.AArch64.regs_kp ((k₁.trans (VG.Proof.X25519.AArch64.kp_wx _ _ _))) fun k hk => by
        obtain ⟨d17, d19, -⟩ := VG.Proof.X25519.AArch64.dreg_facts k hk
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨d19, d17⟩)
    refine WP.mono (VG.Proof.X25519.AArch64.accs_ok is (fun i hi => h i (List.mem_cons_of_mem _ hi)) _) fun s₃ ⟨e₃, k₃, m₃⟩ =>
      ⟨?_, ((k₁.trans (VG.Proof.X25519.AArch64.kp_wx _ _ _)).trans k₃).sub (by sub_regs), by rw [m₃, VG.Proof.X25519.AArch64.mem_wx, m₁]⟩
    rw [e₃, r₂, List.foldl_cons, VG.Proof.X25519.AArch64.v, VG.Proof.X25519.AArch64.gpr_wx_self, BitVec.toNat_add, ← VG.Proof.X25519.AArch64.v, ← VG.Proof.X25519.AArch64.v, e₁,
      show VG.Proof.X25519.AArch64.v s₁ .x17 = VG.Proof.X25519.AArch64.v s .x17 by rw [VG.Proof.X25519.AArch64.v, VG.Proof.X25519.AArch64.v, k₁.gpr _ (by decide)]]

theorem wordLimbs_facts : ∀ j < 4, ∀ i ∈ wordLimbs j, i < 15 ∧ 64 * j < 17 * i + 17 ∧ 17 * i < 64 * j + 64 := by
  decide

theorem wordLimbs_ne : ∀ j < 4, wordLimbs j ≠ [] := by decide

/-- The output region. -/
abbrev outR (o : Addr) : Region := ⟨o, 32⟩

theorem packWord_ok {o : Addr} {s : State} (hx0 : s.gpr .x0 = o) (hw : VG.Proof.X25519.AArch64.outR o ∈ s.wr) {j : Nat} (hj : j < 4) :
    WP isa (.block (packWord j)) s fun s' =>
      ∃ x : BitVec 64, x.toNat = VG.Proof.X25519.AArch64.packV (VG.Proof.X25519.AArch64.regs s) j ∧ s'.mem = s.mem.writeW (o + BitVec.ofNat 64 (8 * j)) x ∧
      VG.Proof.X25519.AArch64.Kp [.x17, .x19] s s' := by
  have hf := VG.Proof.X25519.AArch64.wordLimbs_facts j hj
  obtain ⟨i, is, h⟩ : ∃ i is, wordLimbs j = i :: is := by
    cases hw : wordLimbs j with
    | nil => exact absurd hw (VG.Proof.X25519.AArch64.wordLimbs_ne j hj)
    | cons i is => exact ⟨i, is, rfl⟩
  simp only [packWord, VG.Proof.X25519.AArch64.packV, h]
  · rw [h] at hf
    obtain ⟨hi, hw'⟩ := hf i List.mem_cons_self
    rw [List.cons_append, show ∀ l : List Instr, place .x17 i j :: l = [place .x17 i j] ++ l from fun _ => rfl]
    refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.place_ok (t := .x17) hi hw') fun s₁ ⟨e₁, k₁, m₁⟩ => ?_)
    refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.accs_ok is (fun i hi => hf i (List.mem_cons_of_mem _ hi)) s₁)
      fun s₂ ⟨e₂, k₂, m₂⟩ => ?_)
    have hx0₂ : s₂.gpr .x0 = o := by rw [k₂.gpr _ (by decide), k₁.gpr _ (by decide), hx0]
    have hin : InRegions s₂.wr (s₂.gpr .x0 + BitVec.ofNat 64 (8 * j)) 8 :=
      ⟨VG.Proof.X25519.AArch64.outR o, by rw [k₂.wr, k₁.wr]; exact hw, by rw [hx0₂]; exact Offset.contains_base o (by omega) (by omega)⟩
    refine WP.block_cons_iff.mpr ⟨_, exec_str_x ⟨by omega, by omega⟩ hin, WP.block_nil ⟨s₂.gpr .x17, ?_, ?_, ?_⟩⟩
    · have r₁ : VG.Proof.X25519.AArch64.regs s₁ = VG.Proof.X25519.AArch64.regs s := VG.Proof.X25519.AArch64.regs_kp k₁ fun k hk => by
        obtain ⟨d17, -⟩ := VG.Proof.X25519.AArch64.dreg_facts k hk; simpa using d17
      rw [← VG.Proof.X25519.AArch64.v, e₂, e₁, r₁]
    · rw [hx0₂, m₂, m₁]
    · exact ⟨fun r hr => (k₁.trans k₂).gpr r (by simp only [List.mem_append]; exact fun h => hr (by
        rcases h with h | h <;> simp_all)), (k₁.trans k₂).rd, (k₁.trans k₂).wr⟩

end VG.Proof.X25519.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.AArch64.Lit`. -/
section

/-!
# X25519 on AArch64: the code as a literal

The field arithmetic is unrolled, so the kernel would build the instructions
again in every check that evaluates the code (constant time, properties of
every instruction): the literal of the code (`materialize_code`,
`Proof/Framework/Lit.lean`) is checked once here instead.
-/

namespace VG

materialize_code Impl.X25519.AArch64.x25519

end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.AArch64.Setup`. -/
section

/-!
# X25519 on AArch64: the setup

`setup` saves our caller's registers, decodes the u-coordinate into `x1` and
`x3` (`decode`), stores the bits of the scalar, clamped, at `BITS` (`bits`),
and sets `x2 = 1`, `z2 = 0`, `z3 = 1` (`initSlots`).
-/

namespace VG.Proof.X25519.AArch64

open VG VG.AArch64 VG.Impl.X25519.AArch64 VG.Spec.X25519 VG.Proof.X25519

/-! ## Saving registers -/

/-- The region of the saved registers. -/
abbrev saveR (b : Addr) : Region := ⟨b, 48⟩

theorem saves_ok {b : Addr} : ∀ n ≤ 6, ∀ s : State, VG.Proof.X25519.AArch64.Sc b s →
    WP isa (.block ((List.range n).map fun k => st (saved.getD k .x19) (SAVE + 8 * k))) s fun s' =>
      (∀ k < n, VG.Proof.X25519.AArch64.wd s'.mem b (SAVE + 8 * k) = VG.Proof.X25519.AArch64.v s (saved.getD k .x19)) ∧ Frame [VG.Proof.X25519.AArch64.saveR b] s.mem s'.mem ∧
        VG.Proof.X25519.AArch64.Kp [] s s'
  | 0, _, s, _ => WP.block_nil ⟨fun k hk => absurd hk (Nat.not_lt_zero _), Frame.refl _ _, Kp.refl _ _⟩
  | n + 1, hn, s, hs => by
    rw [List.range_succ, List.map_append, List.map_singleton]
    refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.saves_ok n (by omega) s hs) fun s₁ ⟨e₁, f₁, k₁⟩ => ?_)
    have hs₁ := hs.of_kp k₁ (by decide)
    have hoff : ∀ k < 6, VG.Proof.X25519.AArch64.Off (SAVE + 8 * k) := fun k hk =>
      ⟨by simp only [SAVE]; omega, by simp only [SAVE]; omega⟩
    refine WP.block_cons_iff.mpr ⟨_, VG.Proof.X25519.AArch64.exec_st hs₁ _ (hoff n (by omega)), WP.block_nil ⟨fun k hk => ?_, ?_, ?_⟩⟩
    · simp only
      rw [VG.Proof.X25519.AArch64.wd_writeW _ _ _ (hoff n (by omega)) (hoff k (by omega))]
      by_cases hkn : k = n
      · subst hkn; rw [ite_eq_left rfl, k₁.gpr _ (List.not_mem_nil)]
      · rw [ite_eq_right (by omega)]
        exact e₁ k (by omega)
    · exact f₁.writeW (List.mem_singleton_self _) _
        (Offset.contains_base b (by simp only [SAVE]; omega) (by simp only [SAVE]; omega))
    · exact ⟨fun r _ => k₁.gpr r List.not_mem_nil, k₁.rd, k₁.wr⟩

theorem save_ok {b : Addr} {s : State} (hs : VG.Proof.X25519.AArch64.Sc b s) :
    WP isa (.block save) s fun s' =>
      (∀ k < 6, VG.Proof.X25519.AArch64.wd s'.mem b (SAVE + 8 * k) = VG.Proof.X25519.AArch64.v s (saved.getD k .x19)) ∧ Frame [VG.Proof.X25519.AArch64.saveR b] s.mem s'.mem ∧
        VG.Proof.X25519.AArch64.Kp [] s s' := VG.Proof.X25519.AArch64.saves_ok 6 (by decide) s hs

/-! ## Decoding the u-coordinate -/

/-- The words of the u-coordinate in their registers. -/
def uws (s : State) (q : Nat) : Nat := VG.Proof.X25519.AArch64.v s (ureg q)

theorem limbOf_ok {s : State} {i : Nat} (hi : i < 15) (hm : s.gpr .x22 = 0x1ffff) :
    WP isa (.block (limbOf i)) s fun s' => VG.Proof.X25519.AArch64.v s' .x17 = VG.Proof.X25519.AArch64.ulimb (VG.Proof.X25519.AArch64.uws s) i ∧ VG.Proof.X25519.AArch64.Kp [.x17, .x19] s s' ∧
      s'.mem = s.mem := by
  have hq : ∀ q < 4, ureg q ≠ .x17 ∧ ureg q ≠ .x19 ∧ ureg q ≠ .x22 := by decide
  have hqi := hq (17 * i / 64) (by omega)
  simp only [limbOf]
  split
  · rename_i h
    apply WP.of_runBlock
    simp only [runBlock_cons, VG.Proof.X25519.AArch64.exec_lsr (show 17 * i % 64 < 64 by omega), runStep_some, VG.Proof.X25519.AArch64.exec_and_x,
      runBlock_nil, Option.some.injEq, exists_eq_left', VG.Proof.X25519.AArch64.gpr_wx_self, VG.Proof.X25519.AArch64.gpr_wx_ne _ _ (show Reg.x22 ≠ .x17 by decide)]
    refine ⟨?_, ((VG.Proof.X25519.AArch64.kp_wx s _ _).trans (VG.Proof.X25519.AArch64.kp_wx _ _ _)).sub (by sub_regs), rfl⟩
    rw [VG.Proof.X25519.AArch64.v, VG.Proof.X25519.AArch64.gpr_wx_self, VG.Proof.X25519.AArch64.and_mask17 _ _ hm, VG.Proof.X25519.AArch64.lsr_toNat, VG.Proof.X25519.AArch64.ulimb, ite_eq_left h]; rfl
  · rename_i h
    have hq1 := hq (17 * i / 64 + 1) (by omega)
    apply WP.of_runBlock
    simp only [runBlock_cons, VG.Proof.X25519.AArch64.exec_lsr (show 17 * i % 64 < 64 by omega), runStep_some,
      VG.Proof.X25519.AArch64.exec_lsl (show 64 - 17 * i % 64 < 64 by omega), VG.Proof.X25519.AArch64.exec_add_x, VG.Proof.X25519.AArch64.exec_and_x,
      runBlock_nil, Option.some.injEq, exists_eq_left', VG.Proof.X25519.AArch64.gpr_wx_self, VG.Proof.X25519.AArch64.gpr_wx_ne _ _ (show Reg.x22 ≠ .x17 by decide),
      VG.Proof.X25519.AArch64.gpr_wx_ne _ _ (show Reg.x22 ≠ .x19 by decide), VG.Proof.X25519.AArch64.gpr_wx_ne _ _ (show Reg.x17 ≠ .x19 by decide),
      VG.Proof.X25519.AArch64.gpr_wx_ne _ _ hq1.1]
    refine ⟨?_, ((((VG.Proof.X25519.AArch64.kp_wx s _ _).trans (VG.Proof.X25519.AArch64.kp_wx _ _ _)).trans (VG.Proof.X25519.AArch64.kp_wx _ _ _)).trans (VG.Proof.X25519.AArch64.kp_wx _ _ _)).sub
      (by sub_regs), rfl⟩
    rw [VG.Proof.X25519.AArch64.v, VG.Proof.X25519.AArch64.gpr_wx_self, VG.Proof.X25519.AArch64.and_mask17 _ _ hm, BitVec.toNat_add, VG.Proof.X25519.AArch64.lsr_toNat, VG.Proof.X25519.AArch64.lsl_toNat, VG.Proof.X25519.AArch64.ulimb, ite_eq_right h]; rfl

theorem ureg_ne : ∀ q < 4, ureg q ∉ [Reg.x17, .x19] := by decide

theorem ureg_ne22 : ∀ q < 4, ureg q ∉ [Reg.x22] := by decide

theorem ulimb_congr {w w' : Nat → Nat} (h : ∀ q < 4, w q = w' q) {i : Nat} (hi : i < 15) :
    VG.Proof.X25519.AArch64.ulimb w i = VG.Proof.X25519.AArch64.ulimb w' i := by
  simp only [VG.Proof.X25519.AArch64.ulimb]
  split
  · rw [h _ (by omega)]
  · rw [h _ (by omega), h (17 * i / 64 + 1) (by omega)]

theorem decodeN_ok {b : Addr} :
    ∀ n ≤ 15, ∀ s : State, VG.Proof.X25519.AArch64.Sc b s → s.gpr .x22 = 0x1ffff →
    WP isa (.block ((List.range n).flatMap fun i => limbOf i ++ [st .x17 (X1 + 8 * i), st .x17 (X3 + 8 * i)]))
      s fun s' =>
      (∀ k < n, VG.Proof.X25519.AArch64.wd s'.mem b (X1 + 8 * k) = VG.Proof.X25519.AArch64.ulimb (VG.Proof.X25519.AArch64.uws s) k ∧ VG.Proof.X25519.AArch64.wd s'.mem b (X3 + 8 * k) = VG.Proof.X25519.AArch64.ulimb (VG.Proof.X25519.AArch64.uws s) k) ∧
      Frame [VG.Proof.X25519.AArch64.slotR b X1, VG.Proof.X25519.AArch64.slotR b X3] s.mem s'.mem ∧ VG.Proof.X25519.AArch64.Kp [.x17, .x19] s s'
  | 0, _, s, _, _ => WP.block_nil ⟨fun k hk => absurd hk (Nat.not_lt_zero _), Frame.refl _ _, Kp.refl _ _⟩
  | n + 1, hn, s, hs, hm => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.decodeN_ok n (by omega) s hs hm) fun s₁ ⟨e₁, f₁, k₁⟩ => ?_)
    have hs₁ := hs.of_kp k₁ (by decide)
    have hm₁ : s₁.gpr .x22 = 0x1ffff := by rw [k₁.gpr _ (by decide), hm]
    have hw : ∀ q < 4, VG.Proof.X25519.AArch64.uws s₁ q = VG.Proof.X25519.AArch64.uws s q := fun q hq => by
      simp only [VG.Proof.X25519.AArch64.uws]; rw [VG.Proof.X25519.AArch64.v, k₁.gpr _ (VG.Proof.X25519.AArch64.ureg_ne q hq)]
    refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.limbOf_ok (i := n) (by omega) hm₁) fun s₂ ⟨e₂, k₂, m₂⟩ => ?_)
    have hs₂ := hs₁.of_kp k₂ (by decide)
    have hX1 : X1 = 64 := rfl
    have hX3 : X3 = 448 := rfl
    have o1 : ∀ k < 15, VG.Proof.X25519.AArch64.Off (X1 + 8 * k) := fun k hk => (VG.Proof.X25519.AArch64.slot_ok (n := 0) (by decide)).off hk
    have o3 : ∀ k < 15, VG.Proof.X25519.AArch64.Off (X3 + 8 * k) := fun k hk => (VG.Proof.X25519.AArch64.slot_ok (n := 3) (by decide)).off hk
    apply WP.of_runBlock
    rw [runBlock_cons, VG.Proof.X25519.AArch64.exec_st hs₂ _ (o1 n (by omega)), runStep_some, runBlock_cons,
      VG.Proof.X25519.AArch64.exec_st (hs₂.mem _) _ (o3 n (by omega)), runStep_some, runBlock_nil]
    refine ⟨_, rfl, fun k hk => ?_, ?_, ⟨fun r hr => ?_, (k₁.trans k₂).rd, (k₁.trans k₂).wr⟩⟩
    · simp only
      rw [VG.Proof.X25519.AArch64.wd_writeW _ _ _ (o3 n (by omega)) (o1 k (by omega)), VG.Proof.X25519.AArch64.wd_writeW _ _ _ (o1 n (by omega)) (o1 k (by omega)),
        VG.Proof.X25519.AArch64.wd_writeW _ _ _ (o3 n (by omega)) (o3 k (by omega)), VG.Proof.X25519.AArch64.wd_writeW _ _ _ (o1 n (by omega)) (o3 k (by omega)),
        m₂]
      by_cases hkn : k = n
      · subst hkn
        rw [ite_eq_right (by omega), ite_eq_left rfl, ite_eq_left rfl, ← VG.Proof.X25519.AArch64.v, e₂,
          VG.Proof.X25519.AArch64.ulimb_congr hw (by omega)]
        exact ⟨rfl, rfl⟩
      · rw [ite_eq_right (by omega), ite_eq_right (by omega),
          ite_eq_right (by omega), ite_eq_right (by omega)]
        exact e₁ k (by omega)
    · rw [← m₂] at f₁
      exact (f₁.writeW List.mem_cons_self _ (VG.Proof.X25519.AArch64.slot_contains b (VG.Proof.X25519.AArch64.slot_ok (n := 0) (by decide)) (by omega))).writeW
        (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ (VG.Proof.X25519.AArch64.slot_contains b (VG.Proof.X25519.AArch64.slot_ok (n := 3) (by decide))
          (by omega))
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      have hr' : r ∉ [Reg.x17, .x19] ++ [Reg.x17, .x19] := by
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨hr, hr⟩
      exact (k₁.trans k₂).gpr r hr'

/-! ## The bits of the scalar -/

theorem write1_apply (m : Mem) (a x : Addr) (w : BitVec 8) : m.write a 1 w x = if x = a then w else m x := by
  by_cases h : x = a
  · subst h
    rw [ite_eq_left rfl]
    show (if (x - x).toNat < 1 then w.extractLsb' (8 * (x - x).toNat) 8 else m x) = w
    rw [BitVec.sub_self, BitVec.toNat_zero, ite_eq_left (by decide)]
    exact BitVec.extractLsb'_eq_self
  · have h1 : ¬ (x - a).toNat < 1 := by
      intro h1
      apply h
      have h0 : (x - a).toNat = 0 := by omega
      have : x - a = 0 := BitVec.eq_of_toNat_eq (h0.trans rfl)
      rw [← BitVec.sub_add_cancel x a, this]; exact BitVec.zero_add a
    rw [ite_eq_right h, Mem.write_apply h1]

/-- Bit `j` of a byte, as a byte. -/
def bitB (kb : Byte) (j : Nat) : Byte := BitVec.ofNat 8 ((kb.toNat >>> j) &&& 1)

/-- The region of the bits of byte `i`. -/
abbrev bitsR (b : Addr) (i : Nat) : Region := ⟨b + BitVec.ofNat 64 (BITS + 8 * i), 8⟩

theorem bitStep_ok {b : Addr} {s : State} (hs : VG.Proof.X25519.AArch64.Sc b s) {i j : Nat} (hi : i < 32) (hj : j < 8)
    (h20 : s.gpr .x20 = 1) :
    WP isa (.block [.lsr .x .x19 .x17 j, .logic .and .x .x19 .x19 .x20, .strb .x19 .x3 (BITS + 8 * i + j)]) s
      fun s' => s'.mem = s.mem.write (b + BitVec.ofNat 64 (BITS + 8 * i + j)) 1
          (BitVec.ofNat 8 ((s.gpr .x17).toNat / 2 ^ j % 2)) ∧ VG.Proof.X25519.AArch64.Kp [.x19] s s' := by
  have hoff : BITS + 8 * i + j < 4096 := by simp only [BITS, slot, NSLOT]; omega
  have hin : InRegions s.wr (b + BitVec.ofNat 64 (BITS + 8 * i + j)) 1 :=
    ⟨VG.Proof.X25519.AArch64.scR b, hs.wr, Offset.contains_base b (by simp only [BITS, slot, NSLOT]; omega) (by omega)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, VG.Proof.X25519.AArch64.exec_lsr (show j < 64 by omega), runStep_some, VG.Proof.X25519.AArch64.exec_and_x, VG.Proof.X25519.AArch64.gpr_wx_self,
    VG.Proof.X25519.AArch64.gpr_wx_ne _ _ (show Reg.x20 ≠ .x19 by decide), h20]
  rw [VG.Proof.X25519.AArch64.exec_strb hoff (by rw [VG.Proof.X25519.AArch64.gpr_wx_ne _ _ (by decide), VG.Proof.X25519.AArch64.gpr_wx_ne _ _ (by decide), hs.x3]; exact hin)]
  simp only [runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left', VG.Proof.X25519.AArch64.mem_wx,
    VG.Proof.X25519.AArch64.gpr_wx_ne _ _ (show Reg.x3 ≠ .x19 by decide), hs.x3, State.read, VG.Proof.X25519.AArch64.gpr_wx_self]
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl⟩⟩
  · congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_and, VG.Proof.X25519.AArch64.lsr_toNat, BitVec.toNat_ofNat,
      show (1 : BitVec 64).toNat = 1 from rfl, Nat.and_one_is_mod, Size.bits]
    omega
  · show (State.write _ _ _ _).gpr r = _
    rw [VG.Proof.X25519.AArch64.gpr_wx_ne _ _ (by simpa using hr), VG.Proof.X25519.AArch64.gpr_wx_ne _ _ (by simpa using hr)]

/-- `x` is not in `[b + d, b + d + n)` if its offset from `b` is outside. -/
theorem not_contains {b : Addr} {d n e : Nat} (h : e < d ∨ d + n ≤ e) (hd : d + n ≤ 2 ^ 64) (he : e < 2 ^ 64) :
    ¬ (⟨b + BitVec.ofNat 64 d, n⟩ : Region).Contains (b + BitVec.ofNat 64 e) 1 := by
  simp only [Region.Contains]
  intro hc
  have := (Offset.lt_iff (b + BitVec.ofNat 64 e) b hd).mp (by omega)
  rw [Mem.sub_ofNat_toNat b he] at this
  omega

theorem bitsN_ok {b : Addr} {i : Nat} (hi : i < 32) : ∀ n ≤ 8, ∀ s : State, VG.Proof.X25519.AArch64.Sc b s → s.gpr .x20 = 1 →
    WP isa (.block ((List.range n).flatMap fun j =>
      [.lsr .x .x19 .x17 j, .logic .and .x .x19 .x19 .x20, .strb .x19 .x3 (BITS + 8 * i + j)])) s fun s' =>
      (∀ j < n, s'.mem (b + BitVec.ofNat 64 (BITS + 8 * i + j)) =
        BitVec.ofNat 8 ((s.gpr .x17).toNat / 2 ^ j % 2)) ∧
      Frame [VG.Proof.X25519.AArch64.bitsR b i] s.mem s'.mem ∧ VG.Proof.X25519.AArch64.Kp [.x19] s s'
  | 0, _, s, _, _ => WP.block_nil ⟨fun j hj => absurd hj (Nat.not_lt_zero _), Frame.refl _ _, Kp.refl _ _⟩
  | n + 1, hn, s, hs, h20 => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.bitsN_ok hi n (by omega) s hs h20) fun s₁ ⟨e₁, f₁, k₁⟩ => ?_)
    have h20₁ : s₁.gpr .x20 = 1 := by rw [k₁.gpr _ (by decide), h20]
    have h17₁ : s₁.gpr .x17 = s.gpr .x17 := k₁.gpr _ (by decide)
    refine WP.mono (VG.Proof.X25519.AArch64.bitStep_ok (hs.of_kp k₁ (by decide)) hi (j := n) (by omega) h20₁) fun s₂ ⟨m₂, k₂⟩ =>
      ⟨fun j hj => ?_, ?_, (k₁.trans k₂).sub (by sub_regs)⟩
    · rw [m₂, VG.Proof.X25519.AArch64.write1_apply]
      by_cases hjn : j = n
      · subst hjn; rw [ite_eq_left rfl, h17₁]
      · rw [ite_eq_right (Offset.add_ofNat_ne b (by simp only [BITS, slot, NSLOT]; omega)
          (by simp only [BITS, slot, NSLOT]; omega) (by omega))]
        exact e₁ j (by omega)
    · rw [m₂]
      exact f₁.write (List.mem_singleton_self _) _ (Offset.contains b (by omega) (by omega)
        (by simp only [BITS, slot, NSLOT]; omega))

theorem bitB_eq (kb : Byte) (j : Nat) : BitVec.ofNat 8 (kb.toNat / 2 ^ j % 2) = VG.Proof.X25519.AArch64.bitB kb j := by
  simp only [VG.Proof.X25519.AArch64.bitB, Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]

theorem bitsOf_ok {b : Addr} {s : State} (hs : VG.Proof.X25519.AArch64.Sc b s) {i : Nat} (hi : i < 32) (h20 : s.gpr .x20 = 1)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 i) 1) :
    WP isa (.block (bitsOf i)) s fun s' =>
      (∀ j < 8, s'.mem (b + BitVec.ofNat 64 (BITS + 8 * i + j)) =
        VG.Proof.X25519.AArch64.bitB (s.mem (s.gpr .x1 + BitVec.ofNat 64 i)) j) ∧
      Frame [VG.Proof.X25519.AArch64.bitsR b i] s.mem s'.mem ∧ VG.Proof.X25519.AArch64.Kp [.x17, .x19] s s' := by
  rw [bitsOf]
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.X25519.AArch64.exec_ldrb (by omega) hin, ?_⟩
  have hs₁ := VG.Proof.X25519.AArch64.sc_ww s ((s.mem.read (s.gpr .x1 + BitVec.ofNat 64 i) 1).setWidth 32) hs (show Reg.x17 ≠ .x3 by decide)
  refine WP.mono (VG.Proof.X25519.AArch64.bitsN_ok hi 8 (by decide) _ hs₁ (by rw [VG.Proof.X25519.AArch64.gpr_ww_ne _ _ (by decide), h20]))
    fun s' ⟨e, f, k⟩ => ⟨fun j hj => ?_, f, ((VG.Proof.X25519.AArch64.kp_ww _ _ _).trans k).sub (by sub_regs)⟩
  rw [e j hj, VG.Proof.X25519.AArch64.gpr_ww_self, VG.Proof.X25519.AArch64.read1_toNat, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (Nat.lt_trans (s.mem _).isLt (by decide)), VG.Proof.X25519.AArch64.bitB_eq]

/-- The region of the bits. -/
abbrev bitsArea (b : Addr) : Region := ⟨b + BitVec.ofNat 64 BITS, 256⟩

theorem bitsR_sub (b : Addr) {i : Nat} (hi : i < 32) : Region.Sub (VG.Proof.X25519.AArch64.bitsR b i) (VG.Proof.X25519.AArch64.bitsArea b) :=
  Offset.sub b (by omega) (by omega)

theorem bitsAll_ok {b sc : Addr} (hdisj : ∀ i < 32, ∀ r ∈ [VG.Proof.X25519.AArch64.bitsArea b], ¬ r.Contains (sc + BitVec.ofNat 64 i) 1) :
    ∀ n ≤ 32, ∀ s : State, VG.Proof.X25519.AArch64.Sc b s → s.gpr .x20 = 1 → s.gpr .x1 = sc →
    (∀ i < 32, InRegions (s.rd ++ s.wr) (sc + BitVec.ofNat 64 i) 1) →
    WP isa (.block ((List.range n).flatMap bitsOf)) s fun s' =>
      (∀ t < 8 * n, s'.mem (b + BitVec.ofNat 64 (BITS + t)) =
        VG.Proof.X25519.AArch64.bitB (s.mem (sc + BitVec.ofNat 64 (t / 8))) (t % 8)) ∧
      Frame [VG.Proof.X25519.AArch64.bitsArea b] s.mem s'.mem ∧ VG.Proof.X25519.AArch64.Kp [.x17, .x19] s s'
  | 0, _, s, _, _, _, _ => WP.block_nil ⟨fun t ht => absurd ht (by omega), Frame.refl _ _, Kp.refl _ _⟩
  | n + 1, hn, s, hs, h20, h1, hin => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.bitsAll_ok hdisj n (by omega) s hs h20 h1 hin) fun s₁ ⟨e₁, f₁, k₁⟩ => ?_)
    have h20₁ : s₁.gpr .x20 = 1 := by rw [k₁.gpr _ (by decide), h20]
    have h1₁ : s₁.gpr .x1 = sc := by rw [k₁.gpr _ (by decide), h1]
    refine WP.mono (VG.Proof.X25519.AArch64.bitsOf_ok (hs.of_kp k₁ (by decide)) (i := n) (by omega) h20₁
      (by rw [h1₁, k₁.rd, k₁.wr]; exact hin n (by omega))) fun s₂ ⟨e₂, f₂, k₂⟩ =>
      ⟨fun t ht => ?_, f₁.trans (f₂.sub fun r hr => ⟨VG.Proof.X25519.AArch64.bitsArea b, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hr]; exact VG.Proof.X25519.AArch64.bitsR_sub b (by omega)⟩),
        (k₁.trans k₂).sub (by sub_regs)⟩
    have hsc : s₁.mem (sc + BitVec.ofNat 64 n) = s.mem (sc + BitVec.ofNat 64 n) := f₁ _ (hdisj n (by omega))
    by_cases htn : t < 8 * n
    · rw [f₂ _ (fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact VG.Proof.X25519.AArch64.not_contains (by omega) (by simp only [BITS, slot, NSLOT]; omega)
          (by simp only [BITS, slot, NSLOT]; omega))]
      exact e₁ t htn
    · have e := e₂ (t - 8 * n) (by omega)
      rw [show BITS + 8 * n + (t - 8 * n) = BITS + t by omega, h1₁, hsc] at e
      rw [e, show t / 8 = n by omega, show t % 8 = t - 8 * n by omega]

/-! ## The initial values -/

theorem zeroStep_ok {b : Addr} {s : State} (hs : VG.Proof.X25519.AArch64.Sc b s) {o i : Nat} (ho : VG.Proof.X25519.AArch64.Off (o + 8 * i))
    (h17 : s.gpr .x17 = 0) :
    WP isa (.block [st .x17 (o + 8 * i)]) s fun s' => ∃ x : BitVec 64, x.toNat = 0 ∧
      s'.mem = s.mem.writeW (b + BitVec.ofNat 64 (o + 8 * i)) x ∧ VG.Proof.X25519.AArch64.Kp [] s s' := by
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.X25519.AArch64.exec_st hs _ ho, WP.block_nil ⟨s.gpr .x17, by rw [h17]; rfl, rfl,
    ⟨fun _ _ => rfl, rfl, rfl⟩⟩⟩

/-- The limbs of `0`, and of `1`. -/
def zeroL (_ : Nat) : Nat := 0
def oneL (i : Nat) : Nat := if i = 0 then 1 else 0

theorem zero_ok {b : Addr} {s : State} (hs : VG.Proof.X25519.AArch64.Sc b s) {o : Nat} (ho : o < 15) (h17 : s.gpr .x17 = 0) :
    WP isa (.block (zero (slot o))) s fun s' =>
      VG.Proof.X25519.AArch64.limbs s'.mem b (slot o) = (fun k => if k < 15 then 0 else 0) ∧
      Frame [VG.Proof.X25519.AArch64.slotR b (slot o)] s.mem s'.mem ∧ VG.Proof.X25519.AArch64.Kp [] s s' :=
  VG.Proof.X25519.AArch64.limbwise_all (VG.Proof.X25519.AArch64.slot_ok ho) (fun i => [st .x17 (slot o + 8 * i)]) [] (by decide) (fun _ _ => 0)
    (fun _ => []) (fun s => s.gpr .x17 = 0) (fun s s' h k => by rw [k.gpr _ (by simp), h])
    (fun i hi s hs h17 => VG.Proof.X25519.AArch64.zeroStep_ok hs ((VG.Proof.X25519.AArch64.slot_ok ho).off hi) h17) (fun _ _ _ _ _ => rfl)
    (fun _ _ _ h => absurd h List.not_mem_nil) hs h17

theorem zero_inv {b : Addr} {s₀ s : State} {vals : Nat → Fe} {bnds : Nat → Option Nat}
    (h : VG.Proof.X25519.AArch64.Inv b s₀ s vals bnds) {o : Nat} (ho : o < 15) (h17 : s.gpr .x17 = 0) :
    WP isa (.block (zero (slot o))) s fun s' =>
      VG.Proof.X25519.AArch64.Inv b s₀ s' (Function.update vals o 0) (Function.update bnds o (some 18)) ∧ VG.Proof.X25519.AArch64.Kp [] s s' :=
  WP.mono (VG.Proof.X25519.AArch64.zero_ok h.sc ho h17) fun s' ⟨e, f, k⟩ =>
    ⟨⟨h.sc.of_kp k (by decide), h.sl.update _ _ (by
      rw [e]
      exact ⟨fun i hi => by simp only [hi, ite_true]; decide, rfl⟩)
      fun n hn hno => VG.Proof.X25519.AArch64.limbs_other ho hn hno f,
    h.kp_sub k (List.nil_subset _), VG.Proof.X25519.AArch64.frame_slot h.fr ho f⟩, k⟩

/-- `[o] = 1`: zero, then limb 0 set to 1. -/
theorem one_inv {b : Addr} {s₀ s : State} {vals : Nat → Fe} {bnds : Nat → Option Nat}
    (h : VG.Proof.X25519.AArch64.Inv b s₀ s vals bnds) {o : Nat} (ho : o < 15) (h17 : s.gpr .x17 = 0) :
    WP isa (.block (zero (slot o) ++ ([.movz .x .x19 1 0, st .x19 (slot o)] : List Instr))) s fun s' =>
      VG.Proof.X25519.AArch64.Inv b s₀ s' (Function.update vals o 1) (Function.update bnds o (some 18)) := by
  have o0 : VG.Proof.X25519.AArch64.Off (slot o) := by have := (VG.Proof.X25519.AArch64.slot_ok ho).off (i := 0) (by decide); simpa using this
  refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.zero_ok h.sc ho h17) fun s₁ ⟨e₁, f₁, k₁⟩ => ?_)
  have hs₁ := h.sc.of_kp k₁ (by decide)
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.X25519.AArch64.exec_movz, ?_⟩
  have hs₂ := VG.Proof.X25519.AArch64.sc_wx s₁ ((1 : BitVec 16).setWidth 64) hs₁ (show Reg.x19 ≠ .x3 by decide)
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.X25519.AArch64.exec_st hs₂ _ o0, WP.block_nil ?_⟩
  have hf : Frame [VG.Proof.X25519.AArch64.slotR b (slot o)] s.mem (s₁.mem.writeW (b + BitVec.ofNat 64 (slot o))
      ((s₁.write .x .x19 ((1 : BitVec 16).setWidth 64)).gpr .x19)) :=
    f₁.writeW (List.mem_singleton_self _) _ (by
      have := VG.Proof.X25519.AArch64.slot_contains b (VG.Proof.X25519.AArch64.slot_ok ho) (k := 0) (by decide); simpa using this)
  refine ⟨⟨hs₂.x3, hs₂.wr⟩, h.sl.update _ _ ?_ fun n hn hno => VG.Proof.X25519.AArch64.limbs_other ho hn hno hf,
    h.kp_sub (k₁.trans (W' := [.x19]) ⟨fun r hr => VG.Proof.X25519.AArch64.gpr_wx_ne _ _ (by simpa using hr), rfl, rfl⟩)
      (by decide), VG.Proof.X25519.AArch64.frame_slot h.fr ho hf⟩
  have e : VG.Proof.X25519.AArch64.limbs (s₁.mem.writeW (b + BitVec.ofNat 64 (slot o)) ((s₁.write .x .x19 ((1 : BitVec 16).setWidth 64)).gpr .x19))
      b (slot o) = fun i => if i < 15 then VG.Proof.X25519.AArch64.oneL i else 0 := funext fun i => by
    simp only [VG.Proof.X25519.AArch64.limbs]
    split
    · rename_i hi
      rw [VG.Proof.X25519.AArch64.wd_writeW _ _ _ o0 ((VG.Proof.X25519.AArch64.slot_ok ho).off hi), VG.Proof.X25519.AArch64.gpr_wx_self]
      by_cases h0 : i = 0
      · subst h0; rw [ite_eq_left (by simp)]; rfl
      · rw [ite_eq_right (by omega), show VG.Proof.X25519.AArch64.wd s₁.mem b (slot o + 8 * i) = VG.Proof.X25519.AArch64.limbs s₁.mem b (slot o) i by
          simp only [VG.Proof.X25519.AArch64.limbs, hi, ite_true], e₁]
        simp only [VG.Proof.X25519.AArch64.oneL, h0, ite_false, hi, ite_true]
    · rfl
  dsimp only
  rw [VG.Proof.X25519.AArch64.mem_wx, e]
  refine ⟨fun i hi => by simp only [hi, ite_true, VG.Proof.X25519.AArch64.oneL]; split <;> decide, ?_⟩
  rfl

/-! ## Decoding, with the loads -/

/-- Word `q` of the 32 bytes at `p`. -/
def uw (m : Mem) (p : Addr) (q : Nat) : Nat := (m.readW (p + BitVec.ofNat 64 (8 * q)) 64).toNat

theorem ldrx_ok {s : State} {t n : Reg} {off : Nat} (ho : off % 8 = 0 ∧ off < 32768)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 8) :
    WP isa (.block [.ldr .x t n off]) s fun s' =>
      s'.gpr t = s.mem.readW (s.gpr n + BitVec.ofNat 64 off) 64 ∧ VG.Proof.X25519.AArch64.Kp [t] s s' ∧ s'.mem = s.mem :=
  WP.block_cons_iff.mpr ⟨_, exec_ldr_x ho hin, WP.block_nil ⟨VG.Proof.X25519.AArch64.gpr_wx_self _ _ _, VG.Proof.X25519.AArch64.kp_wx _ _ _, rfl⟩⟩

theorem loadU_ok {s : State} {pt : Addr} (h2 : s.gpr .x2 = pt)
    (hin : ∀ q < 4, InRegions (s.rd ++ s.wr) (pt + BitVec.ofNat 64 (8 * q)) 8) :
    WP isa (.block loadU) s fun s' => (∀ q < 4, VG.Proof.X25519.AArch64.v s' (ureg q) = VG.Proof.X25519.AArch64.uw s.mem pt q) ∧
      VG.Proof.X25519.AArch64.Kp [.x4, .x5, .x6, .x7] s s' ∧ s'.mem = s.mem := by
  rw [loadU, show ∀ (a c d e : Instr), [a, c, d, e] = [a] ++ ([c] ++ ([d] ++ [e])) from fun _ _ _ _ => rfl]
  refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.ldrx_ok (s := s) (t := .x4) (off := 0) (by decide)
    (by rw [h2]; exact hin 0 (by decide))) fun s₁ ⟨e₁, k₁, m₁⟩ => ?_)
  have g₁ : s₁.gpr .x2 = pt := by rw [k₁.gpr _ (by decide), h2]
  refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.ldrx_ok (s := s₁) (t := .x5) (off := 8) (by decide)
    (by rw [g₁, k₁.rd, k₁.wr]; exact hin 1 (by decide))) fun s₂ ⟨e₂, k₂, m₂⟩ => ?_)
  have g₂ : s₂.gpr .x2 = pt := by rw [k₂.gpr _ (by decide), g₁]
  refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.ldrx_ok (s := s₂) (t := .x6) (off := 16) (by decide)
    (by rw [g₂, k₂.rd, k₂.wr, k₁.rd, k₁.wr]; exact hin 2 (by decide))) fun s₃ ⟨e₃, k₃, m₃⟩ => ?_)
  have g₃ : s₃.gpr .x2 = pt := by rw [k₃.gpr _ (by decide), g₂]
  refine WP.mono (VG.Proof.X25519.AArch64.ldrx_ok (s := s₃) (t := .x7) (off := 24) (by decide)
    (by rw [g₃, k₃.rd, k₃.wr, k₂.rd, k₂.wr, k₁.rd, k₁.wr]; exact hin 3 (by decide))) fun s₄ ⟨e₄, k₄, m₄⟩ =>
    ⟨fun q hq => ?_, (((k₁.trans k₂).trans k₃).trans k₄).sub (by sub_regs), by rw [m₄, m₃, m₂, m₁]⟩
  rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3) with rfl | rfl | rfl | rfl
  · show VG.Proof.X25519.AArch64.v s₄ .x4 = _
    rw [VG.Proof.X25519.AArch64.v, k₄.gpr _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide), e₁, h2]; rfl
  · show VG.Proof.X25519.AArch64.v s₄ .x5 = _
    rw [VG.Proof.X25519.AArch64.v, k₄.gpr _ (by decide), k₃.gpr _ (by decide), e₂, g₁, m₁]; rfl
  · show VG.Proof.X25519.AArch64.v s₄ .x6 = _
    rw [VG.Proof.X25519.AArch64.v, k₄.gpr _ (by decide), e₃, g₂, m₂, m₁]; rfl
  · show VG.Proof.X25519.AArch64.v s₄ .x7 = _
    rw [VG.Proof.X25519.AArch64.v, e₄, g₃, m₃, m₂, m₁]; rfl

/-- The limbs of the u-coordinate (zero beyond the fifteenth). -/
def ulimbF (w : Nat → Nat) (i : Nat) : Nat := if i < 15 then VG.Proof.X25519.AArch64.ulimb w i else 0

theorem decode_ok {b pt : Addr} {s : State} (hs : VG.Proof.X25519.AArch64.Sc b s) (h2 : s.gpr .x2 = pt)
    (hin : ∀ q < 4, InRegions (s.rd ++ s.wr) (pt + BitVec.ofNat 64 (8 * q)) 8) :
    WP isa (.block decode) s fun s' =>
      VG.Proof.X25519.AArch64.limbs s'.mem b X1 = VG.Proof.X25519.AArch64.ulimbF (VG.Proof.X25519.AArch64.uw s.mem pt) ∧ VG.Proof.X25519.AArch64.limbs s'.mem b X3 = VG.Proof.X25519.AArch64.ulimbF (VG.Proof.X25519.AArch64.uw s.mem pt) ∧
      Frame [VG.Proof.X25519.AArch64.slotR b X1, VG.Proof.X25519.AArch64.slotR b X3] s.mem s'.mem ∧ VG.Proof.X25519.AArch64.Kp [.x4, .x5, .x6, .x7, .x22, .x17, .x19] s s' := by
  rw [decode, List.append_assoc]
  refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.loadU_ok h2 hin) fun s₁ ⟨e₁, k₁, m₁⟩ => ?_)
  refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.mask17_ok s₁) fun s₂ ⟨e₂, k₂, m₂⟩ => ?_)
  have hs₂ := (hs.of_kp k₁ (by decide)).of_kp k₂ (by decide)
  refine WP.mono (VG.Proof.X25519.AArch64.decodeN_ok 15 (by decide) s₂ hs₂ e₂) fun s₃ ⟨e₃, f₃, k₃⟩ => ?_
  have hu : ∀ i < 15, VG.Proof.X25519.AArch64.ulimb (VG.Proof.X25519.AArch64.uws s₂) i = VG.Proof.X25519.AArch64.ulimb (VG.Proof.X25519.AArch64.uw s.mem pt) i := fun i hi =>
    VG.Proof.X25519.AArch64.ulimb_congr (fun q hq => by
      simp only [VG.Proof.X25519.AArch64.uws]; rw [VG.Proof.X25519.AArch64.v, k₂.gpr _ (VG.Proof.X25519.AArch64.ureg_ne22 q hq), ← VG.Proof.X25519.AArch64.v, e₁ q hq]) hi
  refine ⟨funext fun i => ?_, funext fun i => ?_, by rw [← m₁, ← m₂]; exact f₃,
    ((k₁.trans k₂).trans k₃).sub (by sub_regs)⟩
  · simp only [VG.Proof.X25519.AArch64.limbs, VG.Proof.X25519.AArch64.ulimbF]; split
    · rename_i hi; rw [(e₃ i hi).1, hu i hi]
    · rfl
  · simp only [VG.Proof.X25519.AArch64.limbs, VG.Proof.X25519.AArch64.ulimbF]; split
    · rename_i hi; rw [(e₃ i hi).2, hu i hi]
    · rfl

theorem ulimbF_rep {w : Nat → Nat} (h0 : w 0 < 2 ^ 64) (h1 : w 1 < 2 ^ 64) (h2 : w 2 < 2 ^ 64) :
    VG.Proof.X25519.AArch64.Bnd (VG.Proof.X25519.AArch64.ulimbF w) 17 ∧ VG.Proof.X25519.AArch64.valN (VG.Proof.X25519.AArch64.ulimbF w) 15 = VG.Proof.X25519.AArch64.uN (w 0) (w 1) (w 2) (w 3) % 2 ^ 255 := by
  refine ⟨fun i hi => ?_, ?_⟩
  · simp only [VG.Proof.X25519.AArch64.ulimbF, hi, ite_true, VG.Proof.X25519.AArch64.ulimb]; split <;> exact Nat.mod_lt _ (by decide)
  · rw [VG.Proof.X25519.AArch64.valN_congr (g := fun i => VG.Proof.X25519.AArch64.uN (w 0) (w 1) (w 2) (w 3) / 2 ^ (17 * i) % 2 ^ 17) fun i hi => by
      simp only [VG.Proof.X25519.AArch64.ulimbF, hi, ite_true]; exact VG.Proof.X25519.AArch64.ulimb_eq h0 h1 h2 i hi, VG.Proof.X25519.AArch64.valN_digits]

/-! ## The clamped bits -/

/-- The byte at `BITS + t`: bit `t` of the clamped scalar with the bytes `kb`. -/
def clampB (kb : Nat → Byte) (t : Nat) : Byte :=
  if t < 3 then 0 else if t = 254 then 1 else VG.Proof.X25519.AArch64.bitB (kb (t / 8)) (t % 8)

theorem bits_ok {b sc : Addr} {s : State} (hs : VG.Proof.X25519.AArch64.Sc b s) (h1 : s.gpr .x1 = sc)
    (hin : ∀ i < 32, InRegions (s.rd ++ s.wr) (sc + BitVec.ofNat 64 i) 1)
    (hdisj : ∀ i < 32, ∀ r ∈ [VG.Proof.X25519.AArch64.bitsArea b], ¬ r.Contains (sc + BitVec.ofNat 64 i) 1) :
    WP isa (.block Impl.X25519.AArch64.bits) s fun s' =>
      (∀ t < 256, s'.mem (b + BitVec.ofNat 64 (BITS + t)) = VG.Proof.X25519.AArch64.clampB (fun i => s.mem (sc + BitVec.ofNat 64 i)) t) ∧
      Frame [VG.Proof.X25519.AArch64.bitsArea b] s.mem s'.mem ∧ VG.Proof.X25519.AArch64.Kp [.x17, .x19, .x20] s s' := by
  simp only [Impl.X25519.AArch64.bits, List.cons_append, List.nil_append]
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.X25519.AArch64.exec_movz, ?_⟩
  have hs₁ := VG.Proof.X25519.AArch64.sc_wx s ((1 : BitVec 16).setWidth 64) hs (show Reg.x20 ≠ .x3 by decide)
  refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.bitsAll_ok hdisj 32 (by decide) _ hs₁ (VG.Proof.X25519.AArch64.gpr_wx_self _ _ _)
    (by rw [VG.Proof.X25519.AArch64.gpr_wx_ne _ _ (by decide), h1]) hin) fun s₂ ⟨e₂, f₂, k₂⟩ => ?_)
  have hs₂ := hs₁.of_kp k₂ (by decide)
  have h20 : s₂.gpr .x20 = 1 := by rw [k₂.gpr _ (by decide), VG.Proof.X25519.AArch64.gpr_wx_self]; rfl
  have c : ∀ t < 256, InRegions s₂.wr (s₂.gpr .x3 + BitVec.ofNat 64 (BITS + t)) 1 := fun t ht => by
    have h1 : BITS + t + 1 ≤ 4096 := by simp only [BITS, slot, NSLOT]; omega
    have h2 : BITS + t < 2 ^ 64 := by simp only [BITS, slot, NSLOT]; omega
    rw [hs₂.x3]
    exact ⟨VG.Proof.X25519.AArch64.scR b, hs₂.wr, Offset.contains_base b h1 h2⟩
  have ne : ∀ t < 256, ∀ u < 256, t ≠ u → b + BitVec.ofNat 64 (BITS + t) ≠ b + BitVec.ofNat 64 (BITS + u) :=
    fun t ht u hu h => Offset.add_ofNat_ne b (by simp only [BITS, slot, NSLOT]; omega)
      (by simp only [BITS, slot, NSLOT]; omega) (by omega)
  have cb : ∀ t < 256, (VG.Proof.X25519.AArch64.bitsArea b).Contains (b + BitVec.ofNat 64 (BITS + t)) 1 := fun t ht =>
    Offset.contains b (by omega) (by omega) (by simp only [BITS, slot, NSLOT]; omega)
  have hclamp : WP isa (.block [.movz .x .x19 0 0, .strb .x19 .x3 BITS, .strb .x19 .x3 (BITS + 1),
      .strb .x19 .x3 (BITS + 2), .strb .x20 .x3 (BITS + 254)]) s₂ fun s' =>
      s'.mem = (((s₂.mem.write (b + BitVec.ofNat 64 (BITS + 0)) 1 0).write (b + BitVec.ofNat 64 (BITS + 1)) 1 0).write
        (b + BitVec.ofNat 64 (BITS + 2)) 1 0).write (b + BitVec.ofNat 64 (BITS + 254)) 1 1 ∧ VG.Proof.X25519.AArch64.Kp [.x19] s₂ s' := by
    refine WP.block_cons_iff.mpr ⟨_, VG.Proof.X25519.AArch64.exec_movz, ?_⟩
    have hs₃ := VG.Proof.X25519.AArch64.sc_wx s₂ ((0 : BitVec 16).setWidth 64) hs₂ (show Reg.x19 ≠ .x3 by decide)
    have g19 : (s₂.write .x .x19 ((0 : BitVec 16).setWidth 64)).gpr .x19 = 0 := VG.Proof.X25519.AArch64.gpr_wx_self _ _ _
    have g20 : (s₂.write .x .x19 ((0 : BitVec 16).setWidth 64)).gpr .x20 = 1 := by
      rw [VG.Proof.X25519.AArch64.gpr_wx_ne _ _ (by decide), h20]
    have k3 : VG.Proof.X25519.AArch64.Kp [.x19] s₂ (s₂.write .x .x19 ((0 : BitVec 16).setWidth 64)) := VG.Proof.X25519.AArch64.kp_wx _ _ _
    have m3 : (s₂.write .x .x19 ((0 : BitVec 16).setWidth 64)).mem = s₂.mem := rfl
    generalize s₂.write .x .x19 ((0 : BitVec 16).setWidth 64) = s₃ at hs₃ g19 g20 k3 m3
    have hst : ∀ (r : Reg) (t : Nat) (s₄ : State), t < 256 → VG.Proof.X25519.AArch64.Sc b s₄ → ∀ (l : List Instr) (Q : State → Prop),
        WP isa (.block l) { s₄ with mem := s₄.mem.write (b + BitVec.ofNat 64 (BITS + t)) 1 ((s₄.read .w r).setWidth 8) }
          Q → WP isa (.block (.strb r .x3 (BITS + t) :: l)) s₄ Q := fun r t s₄ ht hs₄ l Q h => by
      have h1 : BITS + t + 1 ≤ 4096 := by simp only [BITS, slot, NSLOT]; omega
      have h2 : BITS + t < 2 ^ 64 := by simp only [BITS, slot, NSLOT]; omega
      have hin : InRegions s₄.wr (s₄.gpr .x3 + BitVec.ofNat 64 (BITS + t)) 1 := by
        rw [hs₄.x3]; exact ⟨VG.Proof.X25519.AArch64.scR b, hs₄.wr, Offset.contains_base b h1 h2⟩
      refine WP.block_cons_iff.mpr ⟨_, VG.Proof.X25519.AArch64.exec_strb (by omega) hin, ?_⟩
      rw [hs₄.x3]
      exact h
    refine hst .x19 0 s₃ (by decide) hs₃ _ _ ?_
    refine hst .x19 1 _ (by decide) (hs₃.mem _) _ _ ?_
    refine hst .x19 2 _ (by decide) ((hs₃.mem _).mem _) _ _ ?_
    refine hst .x20 254 _ (by decide) (((hs₃.mem _).mem _).mem _) _ _ (WP.block_nil ⟨?_, ⟨k3.gpr, k3.rd, k3.wr⟩⟩)
    simp only [State.read, g19, g20, m3]
    rfl
  refine WP.mono hclamp fun s' ⟨m', k'⟩ => ⟨fun t ht => ?_, ?_, ((VG.Proof.X25519.AArch64.kp_wx s _ _).trans (k₂.trans k')).sub
    (by sub_regs)⟩
  · have e := e₂ t (by omega)
    simp only [VG.Proof.X25519.AArch64.mem_wx] at e
    rw [m', VG.Proof.X25519.AArch64.write1_apply, VG.Proof.X25519.AArch64.write1_apply, VG.Proof.X25519.AArch64.write1_apply, VG.Proof.X25519.AArch64.write1_apply]
    simp only [VG.Proof.X25519.AArch64.clampB]
    by_cases h254 : t = 254
    · subst h254; rw [ite_eq_left rfl, ite_eq_right (by decide), ite_eq_left rfl]
    rw [ite_eq_right (ne t ht 254 (by decide) h254), ite_eq_right h254]
    by_cases h2 : t = 2
    · subst h2; rw [ite_eq_left rfl, ite_eq_left (by decide)]
    rw [ite_eq_right (ne t ht 2 (by decide) h2)]
    by_cases h1 : t = 1
    · subst h1; rw [ite_eq_left rfl, ite_eq_left (by decide)]
    rw [ite_eq_right (ne t ht 1 (by decide) h1)]
    by_cases h0 : t = 0
    · subst h0; rw [ite_eq_left rfl, ite_eq_left (by decide)]
    rw [ite_eq_right (ne t ht 0 (by decide) h0), ite_eq_right (by omega), e]
  · simp only [VG.Proof.X25519.AArch64.mem_wx] at f₂
    rw [m']
    exact (((f₂.write (List.mem_singleton_self _) _ (cb 0 (by decide))).write
      (List.mem_singleton_self _) _ (cb 1 (by decide))).write (List.mem_singleton_self _) _ (cb 2 (by decide))).write
      (List.mem_singleton_self _) _ (cb 254 (by decide))

end VG.Proof.X25519.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.AArch64.Main`. -/
section

/-!
# X25519 on AArch64: the whole function
-/

namespace VG.Proof.X25519.AArch64

open VG VG.AArch64 VG.Impl.X25519.AArch64 VG.Spec.X25519 VG.Proof.X25519

/-! ## The swap after the ladder -/

theorem lastSwap_ok {b : Addr} {s : State} {x1 : Fe} {st : Ladder} (hs : VG.Proof.X25519.AArch64.Sc b s)
    (hsl : VG.Proof.X25519.AArch64.Sl s.mem b (VG.Proof.X25519.AArch64.lvals x1 st) VG.Proof.X25519.AArch64.lbnds) (hsw : st.swap ≤ 1) (h24 : s.gpr .x24 = BitVec.ofNat 64 st.swap) :
    WP isa (.block lastSwap) s fun s' => VG.Proof.X25519.AArch64.Sc b s' ∧ (∃ vals, VG.Proof.X25519.AArch64.Sl s'.mem b vals VG.Proof.X25519.AArch64.lbnds ∧
      vals 1 = (cswap st.swap st.x2 st.x3).1 ∧ vals 2 = (cswap st.swap st.z2 st.z3).1) ∧
      VG.Proof.X25519.AArch64.Kp VG.Proof.X25519.AArch64.fieldRegs s s' ∧ Frame [VG.Proof.X25519.AArch64.slotArea b] s.mem s'.mem := by
  have e : lastSwap = ([.addImm .x .x20 .x24 0] ++ maskOf) ++
      (Impl.X25519.AArch64.cswap (slot 1) (slot 3) ++ Impl.X25519.AArch64.cswap (slot 2) (slot 4)) := by
    simp only [lastSwap, List.append_assoc, X2, X3, Z2, Z3]
  rw [e]
  have h1 : WP isa (.block ([.addImm .x .x20 .x24 0] ++ maskOf)) s fun s₁ =>
      s₁.gpr .x22 = VG.Proof.X25519.AArch64.maskB (st.swap == 1) ∧ VG.Proof.X25519.AArch64.Kp [.x20, .x22] s s₁ ∧ s₁.mem = s.mem := by
    apply WP.of_runBlock
    simp only [maskOf, List.cons_append, List.nil_append, runBlock_cons, exec_addImm_x (show 0 < 4096 by decide),
      runStep_some, VG.Proof.X25519.AArch64.exec_movz, VG.Proof.X25519.AArch64.exec_sub_x, VG.Proof.X25519.AArch64.read_x, runBlock_nil, Option.some.injEq, exists_eq_left',
      VG.Proof.X25519.AArch64.gpr_wx_self, VG.Proof.X25519.AArch64.gpr_wx_ne _ _ (show Reg.x20 ≠ .x22 by decide), h24, BitVec.add_zero]
    refine ⟨?_, (((VG.Proof.X25519.AArch64.kp_wx s _ _).trans (VG.Proof.X25519.AArch64.kp_wx _ _ _)).trans (VG.Proof.X25519.AArch64.kp_wx _ _ _)).sub (by sub_regs), rfl⟩
    rw [show BitVec.setWidth 64 (0 : BitVec 16) = 0 from rfl, VG.Proof.X25519.AArch64.maskB_of hsw]
  refine WP.block_append (WP.mono h1 fun s₁ ⟨e₁, k₁, m₁⟩ => ?_)
  have hI : VG.Proof.X25519.AArch64.Inv b s₁ s₁ (VG.Proof.X25519.AArch64.lvals x1 st) VG.Proof.X25519.AArch64.lbnds := Inv.of_sl (hs.of_kp k₁ (by decide)) (by rw [m₁]; exact hsl)
  refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.cswap_inv hI (x := 1) (y := 3) (by decide) (by decide) (by decide)
    (k := 18) rfl rfl e₁) fun s₂ ⟨h₂, g₂⟩ => ?_)
  refine WP.mono (VG.Proof.X25519.AArch64.cswap_inv h₂ (x := 2) (y := 4) (by decide) (by decide) (by decide)
    (k := 18) (sw := st.swap) rfl rfl (by rw [g₂, e₁])) fun s₃ ⟨h₃, _⟩ => ⟨h₃.sc, ⟨_, h₃.sl, ?_, ?_⟩, (k₁.trans h₃.kp).sub
      (List.append_subset.mpr ⟨by decide, List.Subset.refl _⟩), by rw [← m₁]; exact h₃.fr⟩
  · simp only [Function.update_apply, VG.Proof.X25519.AArch64.lvals, ite_true, ite_false, Nat.reduceEqDiff]
  · simp only [Function.update_apply, VG.Proof.X25519.AArch64.lvals, ite_true, ite_false, Nat.reduceEqDiff]

/-! ## The initial values -/

theorem initSlots_ok {b : Addr} {s : State} {vals : Nat → Fe} {bnds : Nat → Option Nat} (hs : VG.Proof.X25519.AArch64.Sc b s)
    (hsl : VG.Proof.X25519.AArch64.Sl s.mem b vals bnds) {x1 : Fe} (h0 : vals 0 = x1) (h3 : vals 3 = x1) (hb0 : bnds 0 = some 18)
    (hb3 : bnds 3 = some 18) :
    WP isa (.block initSlots) s fun s' => VG.Proof.X25519.AArch64.Sc b s' ∧ VG.Proof.X25519.AArch64.Sl s'.mem b (VG.Proof.X25519.AArch64.lvals x1 (init x1)) VG.Proof.X25519.AArch64.lbnds ∧
      VG.Proof.X25519.AArch64.Kp VG.Proof.X25519.AArch64.fieldRegs s s' ∧ Frame [VG.Proof.X25519.AArch64.slotArea b] s.mem s'.mem := by
  have e : initSlots = [.movz .x .x17 0 0] ++ (zero (slot 2) ++ ((zero (slot 1) ++ [.movz .x .x19 1 0, st .x19 (slot 1)])
      ++ copy (slot 4) (slot 1))) := by
    simp only [initSlots, List.append_assoc, X2, Z2, Z3]
  rw [e, List.singleton_append]
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.X25519.AArch64.exec_movz, ?_⟩
  have hI : VG.Proof.X25519.AArch64.Inv b (s.write .x .x17 ((0 : BitVec 16).setWidth 64)) (s.write .x .x17 ((0 : BitVec 16).setWidth 64))
      vals bnds := Inv.of_sl (VG.Proof.X25519.AArch64.sc_wx _ _ hs (by decide)) (by rw [VG.Proof.X25519.AArch64.mem_wx]; exact hsl)
  refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.zero_inv hI (o := 2) (by decide) (VG.Proof.X25519.AArch64.gpr_wx_self _ _ _)) fun s₁ ⟨h₁, k₁⟩ => ?_)
  have g17 : s₁.gpr .x17 = 0 := by
    rw [k₁.gpr _ (by simp), VG.Proof.X25519.AArch64.gpr_wx_self]; rfl
  refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.one_inv h₁ (o := 1) (by decide) g17) fun s₂ h₂ => ?_)
  refine WP.mono (VG.Proof.X25519.AArch64.copy_inv h₂ (o := 4) (a := 1) (by decide) (by decide) (ka := 18) (by simp)) fun s₃ h₃ =>
    ⟨h₃.sc, h₃.sl.weaken fun n hn j hj => ?_, ((VG.Proof.X25519.AArch64.kp_wx _ _ _).trans h₃.kp).sub (List.append_subset.mpr
      ⟨by decide, List.Subset.refl _⟩), by rw [← VG.Proof.X25519.AArch64.mem_wx s .x17 ((0 : BitVec 16).setWidth 64)]; exact h₃.fr⟩
  simp only [VG.Proof.X25519.AArch64.lbnds] at hj
  split at hj
  · cases hj
    rename_i h5
    rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4) with rfl | rfl | rfl | rfl | rfl <;>
      simp [VG.Proof.X25519.AArch64.lvals, init, h0, h3, hb0, hb3]
  · cases hj

/-! ## Packing and restoring -/

theorem packN_ok {o : Addr} : ∀ n ≤ 4, ∀ s : State, s.gpr .x0 = o → VG.Proof.X25519.AArch64.outR o ∈ s.wr →
    WP isa (.block ((List.range n).flatMap packWord)) s fun s' =>
      (∀ j < n, (s'.mem.readW (o + BitVec.ofNat 64 (8 * j)) 64).toNat = VG.Proof.X25519.AArch64.packV (VG.Proof.X25519.AArch64.regs s) j) ∧
      Frame [VG.Proof.X25519.AArch64.outR o] s.mem s'.mem ∧ VG.Proof.X25519.AArch64.Kp [.x17, .x19] s s'
  | 0, _, s, _, _ => WP.block_nil ⟨fun j hj => absurd hj (Nat.not_lt_zero _), Frame.refl _ _, Kp.refl _ _⟩
  | n + 1, hn, s, hx0, hw => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.packN_ok n (by omega) s hx0 hw) fun s₁ ⟨e₁, f₁, k₁⟩ => ?_)
    have r₁ : VG.Proof.X25519.AArch64.regs s₁ = VG.Proof.X25519.AArch64.regs s := VG.Proof.X25519.AArch64.regs_kp k₁ fun k hk => by
      obtain ⟨d17, d19, -⟩ := VG.Proof.X25519.AArch64.dreg_facts k hk; simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨d17, d19⟩
    refine WP.mono (VG.Proof.X25519.AArch64.packWord_ok (o := o) (by rw [k₁.gpr _ (by decide), hx0]) (by rw [k₁.wr]; exact hw) (j := n) (by omega))
      fun s₂ ⟨x, hx, m₂, k₂⟩ => ⟨fun j hj => ?_, ?_, (k₁.trans k₂).sub (by sub_regs)⟩
    · rw [m₂]
      by_cases hjn : j = n
      · subst hjn; rw [Mem.readW_writeW_self64, hx, r₁]
      · rw [Mem.readW_writeW_sep (Offset.sep o (by omega) (by omega) (by omega)) (by decide)]
        exact e₁ j (by omega)
    · rw [m₂]
      exact f₁.writeW (List.mem_singleton_self _) _ (Offset.contains_base o (by omega) (by omega))

theorem saved_mem : ∀ n < 6, saved.getD n .x19 ∈ saved := by decide

theorem saved_ne : ∀ k < 6, ∀ n < 6, k ≠ n → saved.getD k .x19 ≠ saved.getD n .x19 := by decide

theorem restoreN_ok {b : Addr} : ∀ n ≤ 6, ∀ s : State, VG.Proof.X25519.AArch64.Sc b s →
    WP isa (.block ((List.range n).map fun k => ld (saved.getD k .x19) (SAVE + 8 * k))) s fun s' =>
      (∀ k < n, s'.gpr (saved.getD k .x19) = s.mem.readW (b + BitVec.ofNat 64 (SAVE + 8 * k)) 64) ∧
      VG.Proof.X25519.AArch64.Kp saved s s' ∧ s'.mem = s.mem
  | 0, _, s, _ => WP.block_nil ⟨fun k hk => absurd hk (Nat.not_lt_zero _), Kp.refl _ _, rfl⟩
  | n + 1, hn, s, hs => by
    rw [List.range_succ, List.map_append, List.map_singleton]
    refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.restoreN_ok n (by omega) s hs) fun s₁ ⟨e₁, k₁, m₁⟩ => ?_)
    have hs₁ := hs.of_kp k₁ (by decide)
    have ho : VG.Proof.X25519.AArch64.Off (SAVE + 8 * n) := ⟨by simp only [SAVE]; omega, by simp only [SAVE]; omega⟩
    refine WP.block_cons_iff.mpr ⟨_, VG.Proof.X25519.AArch64.exec_ld hs₁ _ ho, WP.block_nil ⟨fun k hk => ?_,
      (k₁.trans (VG.Proof.X25519.AArch64.kp_wx _ _ _)).sub (List.append_subset.mpr ⟨List.Subset.refl _, by
        simp only [List.cons_subset, List.nil_subset, and_true]; exact VG.Proof.X25519.AArch64.saved_mem n (by omega)⟩),
        by rw [VG.Proof.X25519.AArch64.mem_wx, m₁]⟩⟩
    by_cases hkn : k = n
    · subst hkn; rw [VG.Proof.X25519.AArch64.gpr_wx_self, m₁]
    · rw [VG.Proof.X25519.AArch64.gpr_wx_ne _ _ (VG.Proof.X25519.AArch64.saved_ne k (by omega) n (by omega) hkn)]; exact e₁ k (by omega)

/-! ## The end -/

theorem finish_ok {b o : Addr} {s : State} (hs : VG.Proof.X25519.AArch64.Sc b s) {vals : Nat → Fe} {bnds : Nat → Option Nat}
    (hsl : VG.Proof.X25519.AArch64.Sl s.mem b vals bnds) (h1 : bnds 1 = some 18) (h14 : bnds 14 = some 18)
    (hx0 : s.gpr .x0 = o) (hw : VG.Proof.X25519.AArch64.outR o ∈ s.wr) (hdo : (VG.Proof.X25519.AArch64.saveR b).Disjoint (VG.Proof.X25519.AArch64.outR o)) :
    WP isa (.block finish) s fun s' =>
      bytesAt s'.mem o 32 = leBytes 32 (vals 1 * vals 14).val ∧
      (∀ k < 6, s'.gpr (saved.getD k .x19) =
        (s.mem.readW (b + BitVec.ofNat 64 (SAVE + 8 * k)) 64)) ∧
      VG.Proof.X25519.AArch64.Kp (VG.Proof.X25519.AArch64.fieldRegs ++ saved) s s' ∧ Frame [VG.Proof.X25519.AArch64.slotArea b, VG.Proof.X25519.AArch64.outR o] s.mem s'.mem := by
  rw [finish, List.append_assoc, List.append_assoc, List.append_assoc]
  refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.mul_inv (Inv.of_sl hs hsl) (o := 1) (a := 1) (c := 14) (by decide)
    (by decide) (by decide) h1 h14 (by decide) (by decide)) fun s₁ h₁ => ?_)
  obtain ⟨rb, rv⟩ := h₁.sl 1 (by decide) 18 (by simp)
  simp only [Function.update_self] at rv
  refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.load_ok h₁.sc (VG.Proof.X25519.AArch64.slot_ok (n := 1) (by decide))) fun s₂ ⟨e₂, k₂, m₂⟩ => ?_)
  refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.freeze_ok s₂) fun s₃ ⟨e₃, k₃, m₃⟩ => ?_)
  have hx0₃ : s₃.gpr .x0 = o := by
    rw [k₃.gpr _ (by decide), k₂.gpr _ (by decide), h₁.kp.gpr _ (by decide), hx0]
  have hw₃ : VG.Proof.X25519.AArch64.outR o ∈ s₃.wr := by rw [k₃.wr, k₂.wr, h₁.kp.wr]; exact hw
  refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.packN_ok 4 (by decide) s₃ hx0₃ hw₃) fun s₄ ⟨e₄, f₄, k₄⟩ => ?_)
  have hs₄ : VG.Proof.X25519.AArch64.Sc b s₄ := ((h₁.sc.of_kp k₂ (by decide)).of_kp k₃ (by decide)).of_kp k₄ (by decide)
  refine WP.mono (VG.Proof.X25519.AArch64.restoreN_ok 6 (by decide) s₄ hs₄) fun s₅ ⟨e₅, k₅, m₅⟩ => ⟨?_, fun k hk => ?_, ?_, ?_⟩
  · -- the result
    have fz := VG.Proof.X25519.AArch64.freezeF_spec (f := VG.Proof.X25519.AArch64.limbs s₁.mem b (slot 1)) rb
    have hX2 : X2 = slot 1 := rfl
    rw [hX2] at e₂
    rw [← e₂, ← e₃] at fz
    obtain ⟨fb, flt, fv⟩ := fz
    have hp := VG.Proof.X25519.AArch64.packV_eq fb
    have hV : (vals 1 * vals 14).val = VG.Proof.X25519.AArch64.valN (VG.Proof.X25519.AArch64.regs s₃) 15 := by
      rw [← rv, ← e₂, ← fv, toFe_val]
      exact Nat.mod_eq_of_lt flt
    rw [m₅, hV]
    refine bytesAt_leBytes_words64 _ _ _ ?_ ?_ ?_ ?_
    · have := e₄ 0 (by decide); rw [hp 0 (by decide)] at this
      simpa using this
    · have := e₄ 1 (by decide); rw [hp 1 (by decide)] at this; exact this
    · have := e₄ 2 (by decide); rw [hp 2 (by decide)] at this; exact this
    · have := e₄ 3 (by decide); rw [hp 3 (by decide)] at this; exact this
  · -- the saved registers
    have hc : (VG.Proof.X25519.AArch64.saveR b).Contains (b + BitVec.ofNat 64 (SAVE + 8 * k)) (64 / 8) :=
      Offset.contains_base b (by simp only [SAVE]; omega) (by simp only [SAVE]; omega)
    rw [e₅ k hk, f₄.readW hc (by simpa using hdo) (by decide), m₃, m₂,
      h₁.fr.readW hc (by simpa using Offset.base_disjoint b (k := 48) (e := 64) (n := 1920) (by decide) (by decide))
        (by decide)]
  · exact ((((h₁.kp.trans k₂).trans k₃).trans k₄).trans k₅).sub (by decide)
  · have f₁ : Frame [VG.Proof.X25519.AArch64.slotArea b, VG.Proof.X25519.AArch64.outR o] s.mem s₁.mem := h₁.fr.mono (by simp)
    have f₄' : Frame [VG.Proof.X25519.AArch64.slotArea b, VG.Proof.X25519.AArch64.outR o] s₃.mem s₄.mem := f₄.mono (by simp)
    rw [m₅]; rw [m₃, m₂] at f₄'; exact f₁.trans f₄'

end VG.Proof.X25519.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.AArch64.Top`. -/
section

/-!
# X25519 on AArch64: the whole function

The contract the proof is written against (the facts of
`Spec.X25519.x25519Contract` it uses, stated for AArch64), and the correctness
of `vg_x25519` against it: every write is in the working space but the
result's, so the arguments are read unchanged, and the callee-saved registers
it uses are restored from the working space.
-/

namespace VG.Proof.X25519

open VG VG.AArch64 in
/-- `vg_x25519(out = x0, scalar = x1, point = x2, scratch = x3)`. -/
def x25519AArch64 : Contract AArch64.isa where
  pre s :=
    let out : Region := ⟨s.gpr .x0, 32⟩
    let scalar : Region := ⟨s.gpr .x1, 32⟩
    let point : Region := ⟨s.gpr .x2, 32⟩
    let scratch : Region := ⟨s.gpr .x3, 4096⟩
    s.rd = [scalar, point] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧
      scalar.Disjoint scratch ∧ point.Disjoint scratch
  post s s' := Spec.X25519.bytesAt s'.mem (s.gpr .x0) 32 =
    Spec.X25519.x25519 (Spec.X25519.bytesAt s.mem (s.gpr .x1) 32)
      (Spec.X25519.bytesAt s.mem (s.gpr .x2) 32)
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

end VG.Proof.X25519

namespace VG.Proof.X25519.AArch64

open VG VG.AArch64 VG.Impl.X25519.AArch64 VG.Spec.X25519 VG.Proof.X25519

/-! ## Regions of the working space, and outside it -/

theorem saveR_disj (b : Addr) {e n : Nat} (h : 48 ≤ e) (he : e + n ≤ 2 ^ 64) :
    (VG.Proof.X25519.AArch64.saveR b).Disjoint ⟨b + BitVec.ofNat 64 e, n⟩ := Offset.base_disjoint b h he

theorem sub_scR (b : Addr) {d n : Nat} (h : d + n ≤ 4096) :
    Region.Sub ⟨b + BitVec.ofNat 64 d, n⟩ (VG.Proof.X25519.AArch64.scR b) := Offset.sub_base b h

/-- A byte of an argument outside the working space is unchanged. -/
theorem byte_out {b p : Addr} {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hs : ∀ r ∈ rs, Region.Sub r (VG.Proof.X25519.AArch64.scR b)) (hd : (⟨p, 32⟩ : Region).Disjoint (VG.Proof.X25519.AArch64.scR b)) {i : Nat}
    (hi : i < 32) : m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i) :=
  hf.bytes (R := ⟨p, 32⟩) (fun r hr => hd.sub_right (hs r hr)) (by show (32 : Nat) ≤ 2 ^ 64; decide) hi

theorem bytesAt_out {b p : Addr} {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hs : ∀ r ∈ rs, Region.Sub r (VG.Proof.X25519.AArch64.scR b)) (hd : (⟨p, 32⟩ : Region).Disjoint (VG.Proof.X25519.AArch64.scR b)) :
    bytesAt m' p 32 = bytesAt m p 32 := by
  simp only [bytesAt]
  exact List.map_congr_left fun i hi => VG.Proof.X25519.AArch64.byte_out hf hs hd (List.mem_range.mp hi)

/-- A saved register's word is unchanged by writes elsewhere. -/
theorem save_frame {b : Addr} {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (VG.Proof.X25519.AArch64.saveR b).Disjoint r) {k : Nat} (hk : k < 6) :
    VG.Proof.X25519.AArch64.wd m' b (SAVE + 8 * k) = VG.Proof.X25519.AArch64.wd m b (SAVE + 8 * k) := by
  simp only [VG.Proof.X25519.AArch64.wd]
  rw [hf.readW (r := VG.Proof.X25519.AArch64.saveR b) (Offset.contains_base b (by simp only [SAVE]; omega)
    (by simp only [SAVE]; omega)) hd (by decide)]

theorem saveR_slotArea (b : Addr) : ∀ r ∈ [VG.Proof.X25519.AArch64.slotArea b], (VG.Proof.X25519.AArch64.saveR b).Disjoint r := fun r hr => by
  rw [List.mem_singleton.mp hr]; exact VG.Proof.X25519.AArch64.saveR_disj b (by decide) (by decide)

/-! ## The arguments, decoded -/

theorem uN_uw (m : Mem) (p : Addr) :
    VG.Proof.X25519.AArch64.uN (VG.Proof.X25519.AArch64.uw m p 0) (VG.Proof.X25519.AArch64.uw m p 1) (VG.Proof.X25519.AArch64.uw m p 2) (VG.Proof.X25519.AArch64.uw m p 3) = leNum (bytesAt m p 32) := by
  rw [leNum_bytesAt_words64]
  have e0 : p + BitVec.ofNat 64 (8 * 0) = p := BitVec.add_zero p
  have e1 : p + BitVec.ofNat 64 (8 * 1) = p + 8 := rfl
  have e2 : p + BitVec.ofNat 64 (8 * 2) = p + 16 := rfl
  have e3 : p + BitVec.ofNat 64 (8 * 3) = p + 24 := rfl
  simp only [VG.Proof.X25519.AArch64.uN, VG.Proof.X25519.AArch64.uw, e0, e1, e2, e3]

theorem u_rep (m : Mem) (p : Addr) :
    VG.Proof.X25519.AArch64.Rep (VG.Proof.X25519.AArch64.ulimbF (VG.Proof.X25519.AArch64.uw m p)) (toFe (decodeUCoordinate (bytesAt m p 32))) 18 := by
  obtain ⟨hb, hv⟩ := VG.Proof.X25519.AArch64.ulimbF_rep (w := VG.Proof.X25519.AArch64.uw m p) (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _)
  refine ⟨hb.mono (by decide), ?_⟩
  show toFe (VG.Proof.X25519.AArch64.valN _ 15) = _
  rw [hv, VG.Proof.X25519.AArch64.uN_uw, decodeUCoordinate_eq (length_bytesAt _ _ _)]

theorem clampB_eq {m m₀ : Mem} {sc : Addr}
    (h : ∀ i < 32, m (sc + BitVec.ofNat 64 i) = m₀ (sc + BitVec.ofNat 64 i)) {t : Nat} (ht : t < 255) :
    VG.Proof.X25519.AArch64.clampB (fun i => m (sc + BitVec.ofNat 64 i)) t =
      BitVec.ofNat 8 (bit (decodeScalar25519 (bytesAt m₀ sc 32)) t) := by
  rw [scalar_bit (length_bytesAt _ _ _) ht]
  simp only [VG.Proof.X25519.AArch64.clampB]
  split_ifs
  · rfl
  · rfl
  · have hg : (bytesAt m₀ sc 32).getD (t / 8) 0 = m₀ (sc + BitVec.ofNat 64 (t / 8)) := by
      simp only [bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_range (show t / 8 < 32 by omega), Option.map_some, Option.getD_some]
    rw [hg, h _ (by omega)]
    rfl

/-! ## The setup -/

theorem setup_ok {b sc pt : Addr} {s : State} (hs : VG.Proof.X25519.AArch64.Sc b s) (h1 : s.gpr .x1 = sc) (h2 : s.gpr .x2 = pt)
    (hsr : (⟨sc, 32⟩ : Region) ∈ s.rd) (hpr : (⟨pt, 32⟩ : Region) ∈ s.rd)
    (hdS : (⟨sc, 32⟩ : Region).Disjoint (VG.Proof.X25519.AArch64.scR b)) (hdP : (⟨pt, 32⟩ : Region).Disjoint (VG.Proof.X25519.AArch64.scR b)) :
    WP isa (.block setup) s fun s' => VG.Proof.X25519.AArch64.Sc b s' ∧
      VG.Proof.X25519.AArch64.Sl s'.mem b (VG.Proof.X25519.AArch64.lvals (toFe (decodeUCoordinate (bytesAt s.mem pt 32)))
        (init (toFe (decodeUCoordinate (bytesAt s.mem pt 32))))) VG.Proof.X25519.AArch64.lbnds ∧
      (∀ t < 255, s'.mem (b + BitVec.ofNat 64 (BITS + t)) =
        BitVec.ofNat 8 (bit (decodeScalar25519 (bytesAt s.mem sc 32)) t)) ∧
      (∀ k < 6, VG.Proof.X25519.AArch64.wd s'.mem b (SAVE + 8 * k) = VG.Proof.X25519.AArch64.v s (saved.getD k .x19)) ∧
      VG.Proof.X25519.AArch64.Kp VG.Proof.X25519.AArch64.fieldRegs s s' := by
  rw [setup, List.append_assoc, List.append_assoc]
  refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.save_ok hs) fun s₁ ⟨sv₁, f₁, k₁⟩ => ?_)
  have hs₁ := hs.of_kp k₁ (by decide)
  have fs₁ : ∀ r ∈ [VG.Proof.X25519.AArch64.saveR b], Region.Sub r (VG.Proof.X25519.AArch64.scR b) := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact Region.sub_of_ble rfl
  refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.decode_ok hs₁ (by rw [k₁.gpr _ (by simp), h2])
    (fun q hq => ⟨_, List.mem_append_left _ (by rw [k₁.rd]; exact hpr),
      Offset.contains_base pt (by omega) (by omega)⟩)) fun s₂ ⟨l1, l3, f₂, k₂⟩ => ?_)
  have hs₂ := hs₁.of_kp k₂ (by decide)
  have fs₂ : ∀ r ∈ [VG.Proof.X25519.AArch64.slotR b X1, VG.Proof.X25519.AArch64.slotR b X3], Region.Sub r (VG.Proof.X25519.AArch64.scR b) := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact VG.Proof.X25519.AArch64.sub_scR b (by decide)
    · exact VG.Proof.X25519.AArch64.sub_scR b (by decide)
  have hin : ∀ i < 32, InRegions (s₂.rd ++ s₂.wr) (sc + BitVec.ofNat 64 i) 1 := fun i hi =>
    ⟨_, List.mem_append_left _ (by rw [k₂.rd, k₁.rd]; exact hsr), Offset.contains_base sc (by omega) (by omega)⟩
  have hdisj : ∀ i < 32, ∀ r ∈ [VG.Proof.X25519.AArch64.bitsArea b], ¬ r.Contains (sc + BitVec.ofNat 64 i) 1 := fun i hi r hr => by
    rw [List.mem_singleton.mp hr]
    exact hdS.sub_right (VG.Proof.X25519.AArch64.sub_scR b (d := BITS) (n := 256) (by decide)) _
      (Offset.contains_base sc (by omega) (by omega))
  refine WP.block_append (WP.mono (VG.Proof.X25519.AArch64.bits_ok hs₂ (by rw [k₂.gpr _ (by decide), k₁.gpr _ (by simp), h1]) hin hdisj)
    fun s₃ ⟨b₃, f₃, k₃⟩ => ?_)
  have hs₃ := hs₂.of_kp k₃ (by decide)
  have R := VG.Proof.X25519.AArch64.u_rep s₁.mem pt
  rw [VG.Proof.X25519.AArch64.bytesAt_out f₁ fs₁ hdP] at R
  have hsl₃ : VG.Proof.X25519.AArch64.Sl s₃.mem b (fun _ => toFe (decodeUCoordinate (bytesAt s.mem pt 32)))
      (fun n => if n = 0 ∨ n = 3 then some 18 else none) := by
    intro n hn k hk
    dsimp only at hk ⊢
    split at hk
    · cases hk
      rename_i h03
      rcases h03 with rfl | rfl
      · rw [VG.Proof.X25519.AArch64.limbs_frame (VG.Proof.X25519.AArch64.slot_ok (n := 0) (by decide)) f₃ (fun r hr => by
          rw [List.mem_singleton.mp hr]; exact Offset.disjoint b (by decide) (by decide) (by decide)),
          show slot 0 = X1 from rfl, l1]
        exact R
      · rw [VG.Proof.X25519.AArch64.limbs_frame (VG.Proof.X25519.AArch64.slot_ok (n := 3) (by decide)) f₃ (fun r hr => by
          rw [List.mem_singleton.mp hr]; exact Offset.disjoint b (by decide) (by decide) (by decide)),
          show slot 3 = X3 from rfl, l3]
        exact R
    · cases hk
  refine WP.mono (VG.Proof.X25519.AArch64.initSlots_ok hs₃ hsl₃ rfl rfl (by decide) (by decide)) fun s₄ ⟨hs₄, sl₄, k₄, f₄⟩ =>
    ⟨hs₄, sl₄, fun t ht => ?_, fun k hk => ?_, (((k₁.trans k₂).trans k₃).trans k₄).sub (by decide)⟩
  · rw [VG.Proof.X25519.AArch64.bits_frame f₄ (by omega), b₃ t (by omega)]
    exact VG.Proof.X25519.AArch64.clampB_eq (fun i hi => by rw [VG.Proof.X25519.AArch64.byte_out f₂ fs₂ hdS hi, VG.Proof.X25519.AArch64.byte_out f₁ fs₁ hdS hi]) ht
  · rw [VG.Proof.X25519.AArch64.save_frame f₄ (VG.Proof.X25519.AArch64.saveR_slotArea b) hk, VG.Proof.X25519.AArch64.save_frame f₃ (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact VG.Proof.X25519.AArch64.saveR_disj b (by decide) (by decide)) hk,
      VG.Proof.X25519.AArch64.save_frame f₂ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact VG.Proof.X25519.AArch64.saveR_disj b (by decide) (by decide)
        · exact VG.Proof.X25519.AArch64.saveR_disj b (by decide) (by decide)) hk]
    exact sv₁ k hk

/-! ## The whole function -/

/-- The precondition, by name. -/
structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [⟨s₀.gpr .x1, 32⟩, ⟨s₀.gpr .x2, 32⟩]
  wr : s₀.wr = [⟨s₀.gpr .x0, 32⟩, ⟨s₀.gpr .x3, 4096⟩]
  out_sc : (⟨s₀.gpr .x0, 32⟩ : Region).Disjoint ⟨s₀.gpr .x3, 4096⟩
  scalar_sc : (⟨s₀.gpr .x1, 32⟩ : Region).Disjoint ⟨s₀.gpr .x3, 4096⟩
  point_sc : (⟨s₀.gpr .x2, 32⟩ : Region).Disjoint ⟨s₀.gpr .x3, 4096⟩

theorem Pre.of (s₀ : State) (h : Proof.X25519.x25519AArch64.pre s₀) : VG.Proof.X25519.AArch64.Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

/-- Each callee-saved register is saved and restored, or never written. -/
theorem preserved_cases : ∀ r ∈ preserved,
    (∃ k < 6, saved.getD k .x19 = r) ∨ r ∉ VG.Proof.X25519.AArch64.loopRegs ++ saved := by decide

theorem correct {s₀ : State} (hp : VG.Proof.X25519.AArch64.Pre s₀) :
    WP isa x25519 s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧
      Proof.X25519.x25519AArch64.post s₀ s' := by
  obtain ⟨b, hb⟩ : ∃ b, s₀.gpr .x3 = b := ⟨_, rfl⟩
  have hs₀ : VG.Proof.X25519.AArch64.Sc b s₀ := ⟨hb, by rw [hp.wr, ← hb]; simp⟩
  refine WP.seq (WP.mono (VG.Proof.X25519.AArch64.setup_ok hs₀ rfl rfl (by rw [hp.rd]; simp) (by rw [hp.rd]; simp)
    (hb ▸ hp.scalar_sc) (hb ▸ hp.point_sc)) fun s₁ ⟨hs₁, sl₁, bits₁, sv₁, k₁⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.X25519.AArch64.ladder_ok hs₁ sl₁ bits₁) fun s₂ ⟨hs₂, sl₂, sw₂, k₂, f₂⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.X25519.AArch64.lastSwap_ok hs₂ sl₂ (ladderAfter_swap_le _ _ (by decide)) sw₂)
    fun s₃ ⟨hs₃, ⟨vals, sl₃, e1, e2⟩, k₃, f₃⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.X25519.AArch64.invert_ok hs₃ sl₃ e2 (by decide) (by decide)) fun s₄ ⟨hs₄, sl₄, k₄, f₄⟩ => ?_)
  have hx0 : s₄.gpr .x0 = s₀.gpr .x0 := by
    rw [k₄.gpr _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide), k₁.gpr _ (by decide)]
  have hw : VG.Proof.X25519.AArch64.outR (s₀.gpr .x0) ∈ s₄.wr := by rw [k₄.wr, k₃.wr, k₂.wr, k₁.wr, hp.wr]; simp
  have hdo : (VG.Proof.X25519.AArch64.saveR b).Disjoint (VG.Proof.X25519.AArch64.outR (s₀.gpr .x0)) :=
    (hb ▸ hp.out_sc).symm.sub_left (Region.sub_of_ble rfl)
  refine WP.mono (VG.Proof.X25519.AArch64.finish_ok hs₄ sl₄ (by simp [VG.Proof.X25519.AArch64.fbnds]) (by simp [VG.Proof.X25519.AArch64.fbnds]) hx0 hw hdo)
    fun s' ⟨r', sv', k', _⟩ => ⟨fun r hr => ?_, ?_⟩
  · rcases VG.Proof.X25519.AArch64.preserved_cases r hr with ⟨k, hk, rfl⟩ | hn
    · rw [sv' k hk]
      apply BitVec.eq_of_toNat_eq
      rw [show (s₀.gpr (saved.getD k .x19)).toNat = VG.Proof.X25519.AArch64.wd s₁.mem b (SAVE + 8 * k) from (sv₁ k hk).symm]
      show VG.Proof.X25519.AArch64.wd s₄.mem b _ = _
      rw [VG.Proof.X25519.AArch64.save_frame f₄ (VG.Proof.X25519.AArch64.saveR_slotArea b) hk, VG.Proof.X25519.AArch64.save_frame f₃ (VG.Proof.X25519.AArch64.saveR_slotArea b) hk,
        VG.Proof.X25519.AArch64.save_frame f₂ (VG.Proof.X25519.AArch64.saveR_slotArea b) hk]
    · exact ((((k₁.trans k₂).trans k₃).trans k₄).trans k').sub (by decide) |>.gpr r hn
  · show bytesAt s'.mem (s₀.gpr .x0) 32 = x25519 (bytesAt s₀.mem (s₀.gpr .x1) 32)
      (bytesAt s₀.mem (s₀.gpr .x2) 32)
    rw [r', x25519_eq]
    dsimp only
    rw [encodeUCoordinate_eq, invert_eq, Function.update_self, Function.update_of_ne (by decide), e1]

theorem x25519_ok (s : State) (hs : Proof.X25519.x25519AArch64.pre s) :
    ∃ t s', Exec isa Impl.X25519.AArch64.x25519 s t s' ∧ abiPreserved s s' ∧
      Proof.X25519.x25519AArch64.post s s' := by
  obtain ⟨t, s', he, h1, h2⟩ := VG.Proof.X25519.AArch64.correct (Pre.of s hs)
  exact ⟨t, s', he, ⟨h1, Exec.sp he, Exec.preservedV he (by lit_decide)⟩, h2⟩

end VG.Proof.X25519.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.AArch64.Verified`. -/
section

/-!
# X25519 on AArch64: `Verified`

Constant time (by taint tracking: the only branches are on the loop counters,
and every address is an argument plus a constant, or the working space plus a
counter), satisfiability, and the shared contract of `Spec/`.
-/

namespace VG.Proof.X25519.AArch64

open VG VG.AArch64

theorem agree₀ {s₁ s₂ : State} (hpub : Proof.X25519.x25519AArch64.pub s₁ s₂) :
    VG.AArch64.Taint.Agree (VG.AArch64.Taint.ofRegs [.x0, .x1, .x2, .x3]) s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x2000, 32⟩, ⟨0x3000, 32⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x4000, 4096⟩]

theorem x25519_ct : ConstantTime isa Proof.X25519.x25519AArch64.pre Proof.X25519.x25519AArch64.pub
    Impl.X25519.AArch64.x25519 :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3])
    (fun _ _ _ _ hp => VG.Proof.X25519.AArch64.agree₀ hp) (by taint_decide)

theorem x25519_verified :
    Verified AArch64.target Impl.X25519.AArch64.x25519 (Spec.X25519.x25519Contract AArch64.abi) :=
  Verified.of_correct VG.Proof.X25519.AArch64.x25519_ok VG.Proof.X25519.AArch64.x25519_ct
    (by sig_implies [Spec.X25519.x25519Contract, Spec.X25519.x25519Sig, AArch64.abi, AArch64.argRegs,
      Proof.X25519.x25519AArch64]
      [sat] using VG.Proof.X25519.AArch64.sat)

end VG.Proof.X25519.AArch64

end
