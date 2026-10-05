import VerifiedGarbage.Spec.Poly1305
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Impl.Poly1305.Arm
import VerifiedGarbage.Proof.Poly1305.Arm.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Poly1305.Stream
import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Spec.Poly1305.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.Poly1305.Arm.Bytes`. -/
section

-- Formerly the module `VerifiedGarbage.Proof.Poly1305.Arm.Common`.
section

section

/-!
# Poly1305 on 32-bit ARM: the arithmetic in radix `2¹³`

The numbers the code computes (see `Impl/Poly1305/Arm.lean`), as natural
numbers: a number is ten limbs `f 0, …, f 9` of 13 bits (`val`), possibly
larger; the columns of a product modulo `p` (`col`); the carries (`carryN`);
the limbs of four 32-bit words (`mlimb`) and back (`toWords`); and the final
reduction.
-/

namespace VG.Proof.Poly1305.Arm

open VG.Spec.Poly1305 (P)

/-! ## `if` -/

theorem iteT {c : Prop} [Decidable c] {α : Type} {a b : α} (h : c) : (if c then a else b) = a := by
  simp only [h, ↓reduceIte]

theorem iteF {c : Prop} [Decidable c] {α : Type} {a b : α} (h : ¬c) : (if c then a else b) = b := by
  simp only [h, ↓reduceIte]

/-! ## Limbs -/

/-- The number whose limbs are `f 0, …, f 9`. -/
def val (f : Nat → Nat) : Nat :=
  f 0 + 2 ^ 13 * f 1 + 2 ^ 26 * f 2 + 2 ^ 39 * f 3 + 2 ^ 52 * f 4 + 2 ^ 65 * f 5 + 2 ^ 78 * f 6 +
    2 ^ 91 * f 7 + 2 ^ 104 * f 8 + 2 ^ 117 * f 9

theorem val_congr {f g : Nat → Nat} (h : ∀ k < 10, f k = g k) : VG.Proof.Poly1305.Arm.val f = VG.Proof.Poly1305.Arm.val g := by
  simp only [VG.Proof.Poly1305.Arm.val, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide),
    h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide)]

/-- `Σ_{j < n} f j`. -/
def rsum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => VG.Proof.Poly1305.Arm.rsum f n + f n

theorem rsum_le {f g : Nat → Nat} (h : ∀ j, f j ≤ g j) : ∀ n, VG.Proof.Poly1305.Arm.rsum f n ≤ VG.Proof.Poly1305.Arm.rsum g n
  | 0 => (Nat.le_refl _)
  | n + 1 => Nat.add_le_add (VG.Proof.Poly1305.Arm.rsum_le h n) (h n)

theorem rsum_mono (f : Nat → Nat) {m n : Nat} (h : m ≤ n) : VG.Proof.Poly1305.Arm.rsum f m ≤ VG.Proof.Poly1305.Arm.rsum f n := by
  induction n with
  | zero => exact Nat.le_of_eq (congrArg (VG.Proof.Poly1305.Arm.rsum f) (Nat.le_zero.mp h))
  | succ n ih =>
    rcases Nat.lt_or_ge m (n + 1) with h' | h'
    · exact Nat.le_trans (ih (by omega_using [h'])) (Nat.le_add_right _ _)
    · exact Nat.le_of_eq (congrArg (VG.Proof.Poly1305.Arm.rsum f) (by omega_using [h, h']))

theorem rsum_const (c : Nat) : ∀ n, VG.Proof.Poly1305.Arm.rsum (fun _ => c) n = n * c
  | 0 => by simp only [VG.Proof.Poly1305.Arm.rsum, Nat.zero_mul]
  | n + 1 => by rw [VG.Proof.Poly1305.Arm.rsum, VG.Proof.Poly1305.Arm.rsum_const c n, Nat.succ_mul]

/-! ## The columns of a product -/

/-- The coefficient of `h j` in column `k` of `h r` modulo `p`. -/
def coef (r : Nat → Nat) (k j : Nat) : Nat := if j ≤ k then r (k - j) else 5 * r (k + 10 - j)

/-- Column `k` after the rows `j' < j` and, of row `j`, the products of `r i`
for `i < n`, which are added to column `(i + j) mod 10`. -/
def psum (h r : Nat → Nat) (j n k : Nat) : Nat :=
  VG.Proof.Poly1305.Arm.rsum (fun j' => h j' * VG.Proof.Poly1305.Arm.coef r k j') j + if (k + 10 - j) % 10 < n then h j * VG.Proof.Poly1305.Arm.coef r k j else 0

/-- Column `k` of `h r` modulo `p`. -/
def col (h r : Nat → Nat) (k : Nat) : Nat := VG.Proof.Poly1305.Arm.rsum (fun j => h j * VG.Proof.Poly1305.Arm.coef r k j) 10

theorem psum_zero (h r : Nat → Nat) (k : Nat) : VG.Proof.Poly1305.Arm.psum h r 0 0 k = 0 := by
  simp only [VG.Proof.Poly1305.Arm.psum, VG.Proof.Poly1305.Arm.rsum, Nat.sub_zero, Nat.add_mod_right, Nat.not_lt_zero, ↓reduceIte, Nat.add_zero]

theorem psum_row (h r : Nat → Nat) (j k : Nat) :
    VG.Proof.Poly1305.Arm.psum h r j 10 k = VG.Proof.Poly1305.Arm.psum h r (j + 1) 0 k := by
  simp only [VG.Proof.Poly1305.Arm.psum, VG.Proof.Poly1305.Arm.rsum, Nat.not_lt_zero, ite_false, Nat.add_zero]
  rw [ite_eq_left_of_eq_true _ _ (eq_true (Nat.mod_lt _ (by decide)))]

theorem psum_ten (h r : Nat → Nat) (k : Nat) : VG.Proof.Poly1305.Arm.psum h r 10 0 k = VG.Proof.Poly1305.Arm.col h r k := by
  simp only [VG.Proof.Poly1305.Arm.psum, Nat.add_sub_cancel, Nat.not_lt_zero, ↓reduceIte, Nat.add_zero, VG.Proof.Poly1305.Arm.col]

/-- The product `r i` of row `j`, for `i < 10`, is `h j * r i`, or `5 * h j * r i`
once `i + j ≥ 10`. -/
theorem psum_step (h r : Nat → Nat) {j i k : Nat} (hj : j < 10) (hi : i < 10) (hk : k < 10) :
    VG.Proof.Poly1305.Arm.psum h r j (i + 1) k =
      if k = (i + j) % 10 then VG.Proof.Poly1305.Arm.psum h r j i k +
        (if i + j < 10 then h j else 5 * h j) * r i
      else VG.Proof.Poly1305.Arm.psum h r j i k := by
  by_cases e : k = (i + j) % 10
  · subst e
    simp only [VG.Proof.Poly1305.Arm.psum, VG.Proof.Poly1305.Arm.coef, ite_true]
    have e1 : ((i + j) % 10 + 10 - j) % 10 = i := by omega_using [hj, hi, hk]
    rw [e1, ite_eq_left_of_eq_true _ _ (eq_true (show i < i + 1 by omega_using [])),
      ite_eq_right_of_eq_false _ _ (eq_false (show ¬ i < i by omega_using []))]
    by_cases hij : i + j < 10
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hij), ite_eq_left_of_eq_true _ _ (eq_true (show j ≤ (i + j) % 10 by omega_using [hj, hi, hk, e1, hij])),
        show (i + j) % 10 - j = i by omega_using [hj, hi, hk, e1, hij]]; omega_using []
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hij),
        ite_eq_right_of_eq_false _ _ (eq_false (show ¬ j ≤ (i + j) % 10 by omega_using [hj, hi, hk, e1, hij])),
        show (i + j) % 10 + 10 - j = i by omega_using [hj, hi, hk, e1, hij], Nat.mul_left_comm, Nat.mul_assoc]; omega_using []
  · have e' : ((k + 10 - j) % 10 < i + 1) = ((k + 10 - j) % 10 < i) := by
      apply propext; omega_using [hj, hk, e]
    simp only [VG.Proof.Poly1305.Arm.psum, e', e, ite_false]

theorem psum_le_col (h r : Nat → Nat) {j n k : Nat} (hj : j < 10) :
    VG.Proof.Poly1305.Arm.psum h r j n k ≤ VG.Proof.Poly1305.Arm.col h r k := by
  simp only [VG.Proof.Poly1305.Arm.psum, VG.Proof.Poly1305.Arm.col]
  have : VG.Proof.Poly1305.Arm.rsum (fun j' => h j' * VG.Proof.Poly1305.Arm.coef r k j') j + h j * VG.Proof.Poly1305.Arm.coef r k j ≤
      VG.Proof.Poly1305.Arm.rsum (fun j' => h j' * VG.Proof.Poly1305.Arm.coef r k j') 10 :=
    VG.Proof.Poly1305.Arm.rsum_mono (fun j' => h j' * VG.Proof.Poly1305.Arm.coef r k j') (show j + 1 ≤ 10 by omega_using [hj])
  split <;> omega_using [this]

theorem rsum_le_of_lt {f g : Nat → Nat} : ∀ n, (∀ j < n, f j ≤ g j) → VG.Proof.Poly1305.Arm.rsum f n ≤ VG.Proof.Poly1305.Arm.rsum g n
  | 0, _ => (Nat.le_refl _)
  | n + 1, h => Nat.add_le_add (VG.Proof.Poly1305.Arm.rsum_le_of_lt n fun j hj => h j (by omega_using [hj])) (h n (by omega_using []))

/-- A bound on every column. -/
theorem col_le {h r : Nat → Nat} {H R : Nat} (hh : ∀ j < 10, h j ≤ H) (hr : ∀ i < 10, r i ≤ R)
    {k : Nat} (hk : k < 10) : VG.Proof.Poly1305.Arm.col h r k ≤ 10 * (H * (5 * R)) := by
  have : ∀ j < 10, h j * VG.Proof.Poly1305.Arm.coef r k j ≤ H * (5 * R) := fun j hj => by
    apply Nat.mul_le_mul (hh j hj)
    simp only [VG.Proof.Poly1305.Arm.coef]; split
    · have := hr (k - j) (by omega_using [hk, hj]); omega_using [this]
    · have := hr (k + 10 - j) (by omega); omega
  have := VG.Proof.Poly1305.Arm.rsum_le_of_lt 10 this
  rw [VG.Proof.Poly1305.Arm.rsum_const] at this
  exact this

theorem P_eq : P = 2 ^ 130 - 5 := rfl

/-! ## The columns of a product, as a number -/

theorem rsum_add (f g : Nat → Nat) : ∀ n, VG.Proof.Poly1305.Arm.rsum (fun j => f j + g j) n = VG.Proof.Poly1305.Arm.rsum f n + VG.Proof.Poly1305.Arm.rsum g n
  | 0 => rfl
  | n + 1 => by simp only [VG.Proof.Poly1305.Arm.rsum, VG.Proof.Poly1305.Arm.rsum_add f g n]; omega_using []

theorem rsum_mul (c : Nat) (f : Nat → Nat) : ∀ n, c * VG.Proof.Poly1305.Arm.rsum f n = VG.Proof.Poly1305.Arm.rsum (fun j => c * f j) n
  | 0 => rfl
  | n + 1 => by rw [VG.Proof.Poly1305.Arm.rsum, VG.Proof.Poly1305.Arm.rsum, Nat.mul_add, VG.Proof.Poly1305.Arm.rsum_mul c f n]

theorem rsum_congr {f g : Nat → Nat} (h : ∀ j, f j = g j) : ∀ n, VG.Proof.Poly1305.Arm.rsum f n = VG.Proof.Poly1305.Arm.rsum g n
  | 0 => rfl
  | n + 1 => by rw [VG.Proof.Poly1305.Arm.rsum, VG.Proof.Poly1305.Arm.rsum, VG.Proof.Poly1305.Arm.rsum_congr h n, h n]

theorem rsum_congr_lt {f g : Nat → Nat} : ∀ n, (∀ j < n, f j = g j) → VG.Proof.Poly1305.Arm.rsum f n = VG.Proof.Poly1305.Arm.rsum g n
  | 0, _ => rfl
  | n + 1, h => by rw [VG.Proof.Poly1305.Arm.rsum, VG.Proof.Poly1305.Arm.rsum, VG.Proof.Poly1305.Arm.rsum_congr_lt n (fun j hj => h j (by omega_using [hj])), h n (by omega_using [])]

theorem modP_of_eq {X V K : Nat} (h : X + 5 * K = V + 2 ^ 130 * K) : V % P = X % P := by
  have : X = V + P * K := by rw [VG.Proof.Poly1305.Arm.P_eq]; omega_using [h]
  rw [this, Nat.add_mul_mod_self_left]

theorem rsum_comm (f : Nat → Nat → Nat) (m : Nat) : ∀ n,
    VG.Proof.Poly1305.Arm.rsum (fun k => VG.Proof.Poly1305.Arm.rsum (fun j => f k j) m) n = VG.Proof.Poly1305.Arm.rsum (fun j => VG.Proof.Poly1305.Arm.rsum (fun k => f k j) n) m
  | 0 => by
    induction m with
    | zero => rfl
    | succ m ih => simp only [VG.Proof.Poly1305.Arm.rsum] at ih ⊢; omega_using [ih]
  | n + 1 => by
    rw [VG.Proof.Poly1305.Arm.rsum, VG.Proof.Poly1305.Arm.rsum_comm f m n, ← VG.Proof.Poly1305.Arm.rsum_add]; rfl

theorem val_eq (f : Nat → Nat) : VG.Proof.Poly1305.Arm.val f = VG.Proof.Poly1305.Arm.rsum (fun k => 2 ^ (13 * k) * f k) 10 := by
  simp only [VG.Proof.Poly1305.Arm.val, VG.Proof.Poly1305.Arm.rsum]; omega_using []

/-- The terms of row `j` of `h r` that wrap around: `2¹³⁰ ≡ 5`. -/
def wrap (r : Nat → Nat) (j : Nat) : Nat := VG.Proof.Poly1305.Arm.rsum (fun i => if 10 ≤ i + j then 2 ^ (13 * (i + j - 10)) * r i else 0) 10

theorem row_wrap (r : Nat → Nat) {j : Nat} (hj : j < 10) :
    2 ^ (13 * j) * VG.Proof.Poly1305.Arm.val r + 5 * VG.Proof.Poly1305.Arm.wrap r j = VG.Proof.Poly1305.Arm.rsum (fun k => 2 ^ (13 * k) * VG.Proof.Poly1305.Arm.coef r k j) 10 + 2 ^ 130 * VG.Proof.Poly1305.Arm.wrap r j := by
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by omega
  all_goals
    simp only [↓reduceIte, Nat.reduceLeDiff, VG.Proof.Poly1305.Arm.val, VG.Proof.Poly1305.Arm.wrap, VG.Proof.Poly1305.Arm.rsum, VG.Proof.Poly1305.Arm.coef, Nat.reduceSub,
      Nat.reduceAdd, Nat.reduceMul, Nat.zero_add, Nat.add_zero, Nat.mul_zero, Nat.mul_add,
      ← Nat.mul_assoc, Nat.reducePow, Nat.mul_one, Nat.one_mul] <;>
    ac_rfl

/-- The columns of `h r`, as a number, are `h r` modulo `p`. -/
theorem val_col (h r : Nat → Nat) : VG.Proof.Poly1305.Arm.val (VG.Proof.Poly1305.Arm.col h r) % P = VG.Proof.Poly1305.Arm.val h * VG.Proof.Poly1305.Arm.val r % P := by
  have e1 : VG.Proof.Poly1305.Arm.val (VG.Proof.Poly1305.Arm.col h r) = VG.Proof.Poly1305.Arm.rsum (fun j => h j * VG.Proof.Poly1305.Arm.rsum (fun k => 2 ^ (13 * k) * VG.Proof.Poly1305.Arm.coef r k j) 10) 10 := by
    rw [VG.Proof.Poly1305.Arm.val_eq, VG.Proof.Poly1305.Arm.rsum_congr (fun k => by rw [VG.Proof.Poly1305.Arm.col, VG.Proof.Poly1305.Arm.rsum_mul]) 10, VG.Proof.Poly1305.Arm.rsum_comm]
    refine VG.Proof.Poly1305.Arm.rsum_congr (fun j => ?_) 10
    rw [VG.Proof.Poly1305.Arm.rsum_mul]
    exact VG.Proof.Poly1305.Arm.rsum_congr (fun k => Nat.mul_left_comm _ _ _) 10
  have e2 : VG.Proof.Poly1305.Arm.val h * VG.Proof.Poly1305.Arm.val r = VG.Proof.Poly1305.Arm.rsum (fun j => h j * (2 ^ (13 * j) * VG.Proof.Poly1305.Arm.val r)) 10 := by
    rw [VG.Proof.Poly1305.Arm.val_eq h, Nat.mul_comm, VG.Proof.Poly1305.Arm.rsum_mul]
    refine VG.Proof.Poly1305.Arm.rsum_congr (fun j => ?_) 10
    rw [Nat.mul_comm (VG.Proof.Poly1305.Arm.val r), Nat.mul_left_comm]
    exact Nat.mul_assoc _ _ _
  have key : VG.Proof.Poly1305.Arm.val h * VG.Proof.Poly1305.Arm.val r + 5 * VG.Proof.Poly1305.Arm.rsum (fun j => h j * VG.Proof.Poly1305.Arm.wrap r j) 10 =
      VG.Proof.Poly1305.Arm.val (VG.Proof.Poly1305.Arm.col h r) + 2 ^ 130 * VG.Proof.Poly1305.Arm.rsum (fun j => h j * VG.Proof.Poly1305.Arm.wrap r j) 10 := by
    rw [e1, e2, VG.Proof.Poly1305.Arm.rsum_mul, VG.Proof.Poly1305.Arm.rsum_mul, ← VG.Proof.Poly1305.Arm.rsum_add, ← VG.Proof.Poly1305.Arm.rsum_add]
    refine VG.Proof.Poly1305.Arm.rsum_congr_lt 10 (fun j hj => ?_)
    have e := congrArg (h j * ·) (VG.Proof.Poly1305.Arm.row_wrap r hj)
    simp only [Nat.mul_add] at e
    rw [Nat.mul_left_comm (h j) 5, Nat.mul_left_comm (h j) (2 ^ 130)] at e
    exact e
  exact VG.Proof.Poly1305.Arm.modP_of_eq key

/-! ## Carrying -/

/-- Column `k`'s bits from 13 up moved to column `k + 1`. -/
def cstep (f : Nat → Nat) (k : Nat) : Nat → Nat :=
  fun j => if j = k then f k % 2 ^ 13 else if j = k + 1 then f (k + 1) + f k / 2 ^ 13 else f j

theorem val_cstep (f : Nat → Nat) {k : Nat} (hk : k < 9) : VG.Proof.Poly1305.Arm.val (VG.Proof.Poly1305.Arm.cstep f k) = VG.Proof.Poly1305.Arm.val f := by
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
    k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 := by omega
  all_goals simp [VG.Proof.Poly1305.Arm.val, VG.Proof.Poly1305.Arm.cstep]; omega_using []

/-- The carries from columns `a`, …, `a + n - 1`, in order. -/
def carryN (f : Nat → Nat) (a : Nat) : Nat → Nat → Nat
  | 0 => f
  | n + 1 => VG.Proof.Poly1305.Arm.cstep (VG.Proof.Poly1305.Arm.carryN f a n) (n + a)

theorem val_carryN (f : Nat → Nat) (a : Nat) : ∀ n, n + a ≤ 9 → VG.Proof.Poly1305.Arm.val (VG.Proof.Poly1305.Arm.carryN f a n) = VG.Proof.Poly1305.Arm.val f
  | 0, _ => rfl
  | n + 1, h => by rw [VG.Proof.Poly1305.Arm.carryN, VG.Proof.Poly1305.Arm.val_cstep _ (by omega_using [h]), VG.Proof.Poly1305.Arm.val_carryN f a n (by omega_using [h])]

theorem carryN_above (f : Nat → Nat) (a : Nat) : ∀ n j, n + a < j → VG.Proof.Poly1305.Arm.carryN f a n j = f j
  | 0, _, _ => rfl
  | n + 1, j, h => by
    simp only [VG.Proof.Poly1305.Arm.carryN, VG.Proof.Poly1305.Arm.cstep, show j ≠ n + a by omega_using [h], show j ≠ n + a + 1 by omega_using [h], ite_false]
    exact VG.Proof.Poly1305.Arm.carryN_above f a n j (by omega_using [h])

theorem carryN_below (f : Nat → Nat) (a : Nat) : ∀ n j, j < a → VG.Proof.Poly1305.Arm.carryN f a n j = f j
  | 0, _, _ => rfl
  | n + 1, j, h => by
    simp only [VG.Proof.Poly1305.Arm.carryN, VG.Proof.Poly1305.Arm.cstep, show j ≠ n + a by omega_using [h], show j ≠ n + a + 1 by omega_using [h], ite_false]
    exact VG.Proof.Poly1305.Arm.carryN_below f a n j h

theorem carryN_lt (f : Nat → Nat) (a : Nat) : ∀ n j, a ≤ j → j < n + a → VG.Proof.Poly1305.Arm.carryN f a n j < 2 ^ 13
  | 0, _, h₁, h₂ => by omega_using [h₁, h₂]
  | n + 1, j, h₁, h₂ => by
    simp only [VG.Proof.Poly1305.Arm.carryN, VG.Proof.Poly1305.Arm.cstep]
    by_cases e : j = n + a
    · simp only [e, ite_true]; exact Nat.mod_lt _ (by decide)
    · simp only [e, show j ≠ n + a + 1 by omega_using [h₂], ite_false]
      exact VG.Proof.Poly1305.Arm.carryN_lt f a n j h₁ (by omega_using [h₂, e])

/-- The column being carried into, if every column is below `2³² - 2¹⁹`. -/
theorem carryN_top (f : Nat → Nat) (a : Nat) (hf : ∀ j < 10, f j < 2 ^ 32 - 2 ^ 19) :
    ∀ n, n + a ≤ 9 → VG.Proof.Poly1305.Arm.carryN f a n (n + a) < 2 ^ 32
  | 0, h => by have := hf a (by omega_using [h]); simp only [VG.Proof.Poly1305.Arm.carryN, Nat.zero_add]; omega_using [this]
  | n + 1, h => by
    have ih := VG.Proof.Poly1305.Arm.carryN_top f a hf n (by omega_using [h])
    have e : n + 1 + a = n + a + 1 := by omega_using []
    simp only [VG.Proof.Poly1305.Arm.carryN, VG.Proof.Poly1305.Arm.cstep, e, show n + a + 1 ≠ n + a by omega_using [], ite_false, ite_true]
    rw [VG.Proof.Poly1305.Arm.carryN_above f a n _ (by omega_using [])]
    have := hf (n + a + 1) (by omega_using [h])
    have : VG.Proof.Poly1305.Arm.carryN f a n (n + a) / 2 ^ 13 < 2 ^ 19 := by omega_using [ih]
    omega

/-- The carry step's sum does not overflow. -/
theorem carryN_step_lt (f : Nat → Nat) (a : Nat) (hf : ∀ j < 10, f j < 2 ^ 32 - 2 ^ 19) (n : Nat)
    (hn : n + a < 9) :
    VG.Proof.Poly1305.Arm.carryN f a n (n + a + 1) + VG.Proof.Poly1305.Arm.carryN f a n (n + a) / 2 ^ 13 < 2 ^ 32 := by
  have := VG.Proof.Poly1305.Arm.carryN_top f a hf n (by omega_using [hn])
  rw [VG.Proof.Poly1305.Arm.carryN_above f a n _ (by omega_using [])]
  have := hf (n + a + 1) (by omega_using [hn])
  omega

/-- After carrying from columns `0, …, 8`, and then adding column 9's bits from 13 up, times 5,
to column 0 and carrying it once more: the result is congruent to the columns modulo `p`
(`p c` less), and its limbs are below `2¹³` but the second, which is below `2¹³ + 2⁹`. -/
def fold (f : Nat → Nat) : Nat → Nat :=
  let F := VG.Proof.Poly1305.Arm.carryN f 0 9
  VG.Proof.Poly1305.Arm.cstep (fun j => if j = 0 then F 0 + 5 * (F 9 / 2 ^ 13) else if j = 9 then F 9 % 2 ^ 13 else F j) 0

theorem fold_0 (f : Nat → Nat) :
    VG.Proof.Poly1305.Arm.fold f 0 = (VG.Proof.Poly1305.Arm.carryN f 0 9 0 + 5 * (VG.Proof.Poly1305.Arm.carryN f 0 9 9 / 2 ^ 13)) % 2 ^ 13 := by
  simp only [VG.Proof.Poly1305.Arm.fold, Nat.reducePow, VG.Proof.Poly1305.Arm.cstep, ↓reduceIte]

theorem fold_1 (f : Nat → Nat) :
    VG.Proof.Poly1305.Arm.fold f 1 = VG.Proof.Poly1305.Arm.carryN f 0 9 1 + (VG.Proof.Poly1305.Arm.carryN f 0 9 0 + 5 * (VG.Proof.Poly1305.Arm.carryN f 0 9 9 / 2 ^ 13)) / 2 ^ 13 := by
  simp [VG.Proof.Poly1305.Arm.fold, VG.Proof.Poly1305.Arm.cstep]

theorem fold_9 (f : Nat → Nat) : VG.Proof.Poly1305.Arm.fold f 9 = VG.Proof.Poly1305.Arm.carryN f 0 9 9 % 2 ^ 13 := by
  simp only [VG.Proof.Poly1305.Arm.fold, Nat.reducePow, VG.Proof.Poly1305.Arm.cstep, reduceCtorEq, ↓reduceIte, Nat.zero_add, Nat.reduceEqDiff]

theorem fold_mid (f : Nat → Nat) {j : Nat} (h1 : 2 ≤ j) (h2 : j < 9) : VG.Proof.Poly1305.Arm.fold f j = VG.Proof.Poly1305.Arm.carryN f 0 9 j := by
  simp only [VG.Proof.Poly1305.Arm.fold, VG.Proof.Poly1305.Arm.cstep]
  simp only [show j ≠ 0 by omega_using [h1, h2], show j ≠ 1 by omega_using [h1, h2], show j ≠ 9 by omega_using [h1, h2], show 0 + 1 = 1 from rfl,
    ite_false]

theorem fold_facts (f : Nat → Nat) (hf : ∀ j < 10, f j < 2 ^ 32 - 2 ^ 19) :
    VG.Proof.Poly1305.Arm.val (VG.Proof.Poly1305.Arm.fold f) % P = VG.Proof.Poly1305.Arm.val f % P ∧ VG.Proof.Poly1305.Arm.val (VG.Proof.Poly1305.Arm.fold f) < 2 ^ 130 + 2 ^ 22 ∧ VG.Proof.Poly1305.Arm.fold f 0 < 2 ^ 13 ∧
      VG.Proof.Poly1305.Arm.fold f 1 < 2 ^ 13 + 2 ^ 9 ∧ ∀ j, 2 ≤ j → j < 10 → VG.Proof.Poly1305.Arm.fold f j < 2 ^ 13 := by
  have hv := VG.Proof.Poly1305.Arm.val_carryN f 0 9 (by decide)
  have ht := VG.Proof.Poly1305.Arm.carryN_top f 0 hf 9 (by decide)
  have hl : ∀ j < 9, VG.Proof.Poly1305.Arm.carryN f 0 9 j < 2 ^ 13 := fun j hj => VG.Proof.Poly1305.Arm.carryN_lt f 0 9 j (by omega_using [hj]) (by omega_using [hj])
  simp only [Nat.add_zero] at ht
  have e : ∀ j, VG.Proof.Poly1305.Arm.fold f j = VG.Proof.Poly1305.Arm.cstep (fun j => if j = 0 then VG.Proof.Poly1305.Arm.carryN f 0 9 0 + 5 * (VG.Proof.Poly1305.Arm.carryN f 0 9 9 / 2 ^ 13)
      else if j = 9 then VG.Proof.Poly1305.Arm.carryN f 0 9 9 % 2 ^ 13 else VG.Proof.Poly1305.Arm.carryN f 0 9 j) 0 j := fun j => rfl
  generalize VG.Proof.Poly1305.Arm.carryN f 0 9 = F at hv ht hl e
  have f0 : VG.Proof.Poly1305.Arm.fold f 0 = (F 0 + 5 * (F 9 / 2 ^ 13)) % 2 ^ 13 := by rw [e]; simp only [VG.Proof.Poly1305.Arm.cstep, ↓reduceIte, Nat.reducePow]
  have f1 : VG.Proof.Poly1305.Arm.fold f 1 = F 1 + (F 0 + 5 * (F 9 / 2 ^ 13)) / 2 ^ 13 := by rw [e]; simp [VG.Proof.Poly1305.Arm.cstep]
  have f9 : VG.Proof.Poly1305.Arm.fold f 9 = F 9 % 2 ^ 13 := by rw [e]; simp only [VG.Proof.Poly1305.Arm.cstep, reduceCtorEq, ↓reduceIte, Nat.zero_add, Nat.reduceEqDiff, Nat.reducePow]
  have fj : ∀ j, 2 ≤ j → j < 9 → VG.Proof.Poly1305.Arm.fold f j = F j := by
    intro j h1 h2
    rw [e]; simp only [VG.Proof.Poly1305.Arm.cstep]
    simp only [show j ≠ 0 by omega_using [h1, h2], show j ≠ 1 by omega_using [h1, h2], show j ≠ 9 by omega_using [h1, h2], show 0 + 1 = 1 from rfl,
      ite_false]
  have l0 := hl 0 (by decide); have l1 := hl 1 (by decide)
  have key : VG.Proof.Poly1305.Arm.val (VG.Proof.Poly1305.Arm.fold f) + P * (F 9 / 2 ^ 13) = VG.Proof.Poly1305.Arm.val F := by
    simp only [VG.Proof.Poly1305.Arm.val, f0, f1, f9, fj 2 (by decide) (by decide), fj 3 (by decide) (by decide),
      fj 4 (by decide) (by decide), fj 5 (by decide) (by decide), fj 6 (by decide) (by decide),
      fj 7 (by decide) (by decide), fj 8 (by decide) (by decide), VG.Proof.Poly1305.Arm.P_eq]
    omega_using []
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← hv, ← key, Nat.add_mul_mod_self_left]
  · have l2 := hl 2 (by decide); have l3 := hl 3 (by decide); have l4 := hl 4 (by decide)
    have l5 := hl 5 (by decide); have l6 := hl 6 (by decide); have l7 := hl 7 (by decide)
    have l8 := hl 8 (by decide)
    simp only [VG.Proof.Poly1305.Arm.val, f0, f1, f9, fj 2 (by decide) (by decide), fj 3 (by decide) (by decide),
      fj 4 (by decide) (by decide), fj 5 (by decide) (by decide), fj 6 (by decide) (by decide),
      fj 7 (by decide) (by decide), fj 8 (by decide) (by decide)]
    omega_using [ht, f9, l0, l1, l2, l3, l4, l5, l6, l7, l8]
  · rw [f0]; exact Nat.mod_lt _ (by decide)
  · rw [f1]; omega_using [ht, f0, f1, f9, l0, l1]
  · intro j h2 h10
    rcases Nat.lt_or_ge j 9 with h | h
    · rw [fj j h2 h]; exact hl j h
    · rw [show j = 9 by omega_using [h2, h10, h], f9]; exact Nat.mod_lt _ (by decide)

/-! ## The limbs of four words -/

/-- Limb `k` of `w0 + 2³² w1 + 2⁶⁴ w2 + 2⁹⁶ w3`, as the code computes it: the
sum of the pieces of the words (`Impl.Poly1305.Arm.pieces`). -/
def mlimb (w0 w1 w2 w3 : Nat) : Nat → Nat
  | 0 => w0 % 2 ^ 13
  | 1 => w0 % 2 ^ 26 / 2 ^ 13
  | 2 => w0 / 2 ^ 26 + w1 % 2 ^ 7 * 2 ^ 6
  | 3 => w1 % 2 ^ 20 / 2 ^ 7
  | 4 => w1 / 2 ^ 20 + w2 % 2 * 2 ^ 12
  | 5 => w2 % 2 ^ 14 / 2
  | 6 => w2 % 2 ^ 27 / 2 ^ 14
  | 7 => w2 / 2 ^ 27 + w3 % 2 ^ 8 * 2 ^ 5
  | 8 => w3 % 2 ^ 21 / 2 ^ 8
  | _ => w3 / 2 ^ 21

theorem mlimb_lt {w0 w1 w2 w3 : Nat} (h0 : w0 < 2 ^ 32) (h1 : w1 < 2 ^ 32) (h2 : w2 < 2 ^ 32)
    (h3 : w3 < 2 ^ 32) (k : Nat) : VG.Proof.Poly1305.Arm.mlimb w0 w1 w2 w3 k < 2 ^ 13 := by
  unfold VG.Proof.Poly1305.Arm.mlimb
  split <;> omega_using [h1, h2, h3, h0]

theorem val_mlimb {w0 w1 w2 w3 : Nat} (h0 : w0 < 2 ^ 32) (h1 : w1 < 2 ^ 32) (h2 : w2 < 2 ^ 32)
    (h3 : w3 < 2 ^ 32) :
    VG.Proof.Poly1305.Arm.val (VG.Proof.Poly1305.Arm.mlimb w0 w1 w2 w3) = w0 + 2 ^ 32 * w1 + 2 ^ 64 * w2 + 2 ^ 96 * w3 := by
  have e0 : w0 = w0 % 2 ^ 13 + 2 ^ 13 * (w0 % 2 ^ 26 / 2 ^ 13) + 2 ^ 26 * (w0 / 2 ^ 26) := by omega_using []
  have e1 : w1 = w1 % 2 ^ 7 + 2 ^ 7 * (w1 % 2 ^ 20 / 2 ^ 7) + 2 ^ 20 * (w1 / 2 ^ 20) := by omega_using []
  have e2 : w2 = w2 % 2 + 2 * (w2 % 2 ^ 14 / 2) + 2 ^ 14 * (w2 % 2 ^ 27 / 2 ^ 14) +
    2 ^ 27 * (w2 / 2 ^ 27) := by omega_using []
  have e3 : w3 = w3 % 2 ^ 8 + 2 ^ 8 * (w3 % 2 ^ 21 / 2 ^ 8) + 2 ^ 21 * (w3 / 2 ^ 21) := by omega_using []
  simp only [VG.Proof.Poly1305.Arm.val, VG.Proof.Poly1305.Arm.mlimb]
  generalize w0 % 2 ^ 13 = a0, w0 % 2 ^ 26 / 2 ^ 13 = a1, w0 / 2 ^ 26 = a2 at *
  generalize w1 % 2 ^ 7 = b0, w1 % 2 ^ 20 / 2 ^ 7 = b1, w1 / 2 ^ 20 = b2 at *
  generalize w2 % 2 = c0, w2 % 2 ^ 14 / 2 = c1, w2 % 2 ^ 27 / 2 ^ 14 = c2, w2 / 2 ^ 27 = c3 at *
  generalize w3 % 2 ^ 8 = d0, w3 % 2 ^ 21 / 2 ^ 8 = d1, w3 / 2 ^ 21 = d2 at *
  subst e0 e1 e2 e3
  omega_using []

/-! ## Words of limbs -/

theorem val_toWords {u : Nat → Nat} (h : ∀ k < 9, u k < 2 ^ 13) :
    VG.Proof.Poly1305.Arm.val u = (u 0 + 2 ^ 13 * u 1 + 2 ^ 26 * (u 2 % 2 ^ 6)) +
      2 ^ 32 * (u 2 / 2 ^ 6 + 2 ^ 7 * u 3 + 2 ^ 20 * (u 4 % 2 ^ 12)) +
      2 ^ 64 * (u 4 / 2 ^ 12 + 2 * u 5 + 2 ^ 14 * u 6 + 2 ^ 27 * (u 7 % 2 ^ 5)) +
      2 ^ 96 * (u 7 / 2 ^ 5 + 2 ^ 8 * u 8 + 2 ^ 21 * (u 9 % 2 ^ 11)) + 2 ^ 128 * (u 9 / 2 ^ 11) := by
  have := h 0 (by decide); have := h 1 (by decide); have := h 2 (by decide); have := h 3 (by decide)
  have := h 4 (by decide); have := h 5 (by decide); have := h 6 (by decide); have := h 7 (by decide)
  have := h 8 (by decide)
  simp only [VG.Proof.Poly1305.Arm.val]
  omega_using []

/-! ## The final reduction -/

/-- The carries of `h + 5` into register `r12`. -/
def chainT (u : Nat → Nat) : Nat → Nat
  | 0 => u 0 + 5
  | k + 1 => u (k + 1) + VG.Proof.Poly1305.Arm.chainT u k / 2 ^ 13

/-- `Σ_{j < k} 2^(13 j) u j`. -/
def spre (u : Nat → Nat) (k : Nat) : Nat := VG.Proof.Poly1305.Arm.rsum (fun j => 2 ^ (13 * j) * u j) k

theorem chainT_eq (u : Nat → Nat) : ∀ k, VG.Proof.Poly1305.Arm.chainT u k = u k + (VG.Proof.Poly1305.Arm.spre u k + 5) / 2 ^ (13 * k)
  | 0 => by simp [VG.Proof.Poly1305.Arm.chainT, VG.Proof.Poly1305.Arm.spre, VG.Proof.Poly1305.Arm.rsum]
  | k + 1 => by
    rw [VG.Proof.Poly1305.Arm.chainT, VG.Proof.Poly1305.Arm.chainT_eq u k]
    congr 1
    have e : VG.Proof.Poly1305.Arm.spre u (k + 1) + 5 = (VG.Proof.Poly1305.Arm.spre u k + 5) + 2 ^ (13 * k) * u k := by
      simp only [VG.Proof.Poly1305.Arm.spre, VG.Proof.Poly1305.Arm.rsum]; omega_using []
    rw [e, show 13 * (k + 1) = 13 * k + 13 by omega_using [], Nat.pow_add, ← Nat.div_div_eq_div_mul,
      Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.add_comm (u k)]

theorem chainT_top (u : Nat → Nat) : VG.Proof.Poly1305.Arm.chainT u 9 / 2 ^ 13 = (VG.Proof.Poly1305.Arm.val u + 5) / 2 ^ 130 := by
  rw [VG.Proof.Poly1305.Arm.chainT_eq, Nat.add_comm (u 9)]
  have e : VG.Proof.Poly1305.Arm.val u + 5 = (VG.Proof.Poly1305.Arm.spre u 9 + 5) + 2 ^ 117 * u 9 := by
    simp only [VG.Proof.Poly1305.Arm.val, VG.Proof.Poly1305.Arm.spre, VG.Proof.Poly1305.Arm.rsum]; omega_using []
  rw [e, show (130 : Nat) = 117 + 13 from rfl, Nat.pow_add, ← Nat.div_div_eq_div_mul,
    Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), show 13 * 9 = 117 from rfl]

/-- Limbs below `2¹³` but the top one, which is masked. -/
theorem val_mask_top {g g' : Nat → Nat} (h : ∀ k < 9, g k < 2 ^ 13) (h' : ∀ k < 9, g' k = g k)
    (h9 : g' 9 = g 9 % 2 ^ 13) : VG.Proof.Poly1305.Arm.val g' = VG.Proof.Poly1305.Arm.val g % 2 ^ 130 := by
  have := h 0 (by decide); have := h 1 (by decide); have := h 2 (by decide); have := h 3 (by decide)
  have := h 4 (by decide); have := h 5 (by decide); have := h 6 (by decide); have := h 7 (by decide)
  have := h 8 (by decide)
  have e : VG.Proof.Poly1305.Arm.val g = VG.Proof.Poly1305.Arm.val g' + 2 ^ 130 * (g 9 / 2 ^ 13) := by
    simp only [VG.Proof.Poly1305.Arm.val, h' 0 (by decide), h' 1 (by decide), h' 2 (by decide), h' 3 (by decide),
      h' 4 (by decide), h' 5 (by decide), h' 6 (by decide), h' 7 (by decide), h' 8 (by decide), h9]
    omega_using []
  have hl : VG.Proof.Poly1305.Arm.val g' < 2 ^ 130 := by
    simp only [VG.Proof.Poly1305.Arm.val, h' 0 (by decide), h' 1 (by decide), h' 2 (by decide), h' 3 (by decide),
      h' 4 (by decide), h' 5 (by decide), h' 6 (by decide), h' 7 (by decide), h' 8 (by decide), h9]
    have : g 9 % 2 ^ 13 < 2 ^ 13 := Nat.mod_lt _ (by decide)
    omega
  rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hl]

/-- The final reduction: with `c = ⌊(h + 5) / 2¹³⁰⌋`, `(h + 5 c) mod 2¹³⁰` is `h mod p`,
for `h < 2 p`. -/
theorem reduce_eq {h : Nat} (hh : h < 2 ^ 131 - 10) :
    (h + 5 * ((h + 5) / 2 ^ 130)) % 2 ^ 130 = h % P := by
  rw [VG.Proof.Poly1305.Arm.P_eq]
  rcases Nat.lt_or_ge (h + 5) (2 ^ 130) with h1 | h1
  · rw [Nat.div_eq_of_lt h1, Nat.mod_eq_of_lt (by omega_using [hh, h1]), Nat.mod_eq_of_lt (by omega_using [hh, h1]), Nat.mul_zero,
      Nat.add_zero]
  · have e : (h + 5) / 2 ^ 130 = 1 := by omega_using [hh, h1]
    rw [e]
    omega_using [hh, h1, e]

/-! ## The whole final reduction -/

theorem chainT_le (u : Nat → Nat) (hu : ∀ j < 10, u j ≤ 2 ^ 13) : ∀ k < 10, VG.Proof.Poly1305.Arm.chainT u k ≤ 2 ^ 13 + 5
  | 0, _ => by have := hu 0 (by decide); simp only [VG.Proof.Poly1305.Arm.chainT]; omega_using [this]
  | k + 1, h => by
    have := VG.Proof.Poly1305.Arm.chainT_le u hu k (by omega_using [h])
    have := hu (k + 1) h
    simp only [VG.Proof.Poly1305.Arm.chainT]
    have : VG.Proof.Poly1305.Arm.chainT u k / 2 ^ 13 ≤ 1 := by omega
    omega

/-- The limbs after `carry2`. -/
def redK (E : Nat → Nat) : Nat → Nat := VG.Proof.Poly1305.Arm.carryN (VG.Proof.Poly1305.Arm.fold E) 1 8
/-- `⌊(h + 5) / 2¹³⁰⌋`. -/
def redC (E : Nat → Nat) : Nat := (VG.Proof.Poly1305.Arm.val (VG.Proof.Poly1305.Arm.redK E) + 5) / 2 ^ 130
/-- The limbs after `addC`. -/
def redK' (E : Nat → Nat) : Nat → Nat := fun j => if j = 0 then VG.Proof.Poly1305.Arm.redK E 0 + 5 * VG.Proof.Poly1305.Arm.redC E else VG.Proof.Poly1305.Arm.redK E j
/-- The limbs after `carry3`. -/
def redL (E : Nat → Nat) : Nat → Nat :=
  fun j => if j = 9 then VG.Proof.Poly1305.Arm.carryN (VG.Proof.Poly1305.Arm.redK' E) 0 9 9 % 2 ^ 13 else VG.Proof.Poly1305.Arm.carryN (VG.Proof.Poly1305.Arm.redK' E) 0 9 j

theorem red_facts (E : Nat → Nat) (hE : ∀ j < 10, E j < 2 ^ 32 - 2 ^ 19) :
    (∀ j < 10, VG.Proof.Poly1305.Arm.fold E j < 2 ^ 32 - 2 ^ 19) ∧ (∀ j < 10, VG.Proof.Poly1305.Arm.redK E j ≤ 2 ^ 13) ∧
      (∀ j < 10, VG.Proof.Poly1305.Arm.redK' E j < 2 ^ 32 - 2 ^ 19) ∧ VG.Proof.Poly1305.Arm.val (VG.Proof.Poly1305.Arm.redL E) = VG.Proof.Poly1305.Arm.val E % P ∧
      ∀ j < 10, VG.Proof.Poly1305.Arm.redL E j < 2 ^ 13 := by
  obtain ⟨hv, hvl, h0, h1, hj⟩ := VG.Proof.Poly1305.Arm.fold_facts E hE
  have hH : ∀ j < 10, VG.Proof.Poly1305.Arm.fold E j < 2 ^ 32 - 2 ^ 19 := fun j hj' => by
    rcases Nat.lt_or_ge j 2 with h | h
    · rcases (by omega_using [hj', h] : j = 0 ∨ j = 1) with rfl | rfl <;> omega_using [h1, h0]
    · have := hj j h hj'; omega_using [this]
  have hvK : VG.Proof.Poly1305.Arm.val (VG.Proof.Poly1305.Arm.redK E) = VG.Proof.Poly1305.Arm.val (VG.Proof.Poly1305.Arm.fold E) := VG.Proof.Poly1305.Arm.val_carryN _ 1 8 (by decide)
  have hK0 : VG.Proof.Poly1305.Arm.redK E 0 = VG.Proof.Poly1305.Arm.fold E 0 := VG.Proof.Poly1305.Arm.carryN_below _ 1 8 0 (by decide)
  have hKm : ∀ j, 1 ≤ j → j < 9 → VG.Proof.Poly1305.Arm.redK E j < 2 ^ 13 := fun j a b => VG.Proof.Poly1305.Arm.carryN_lt _ 1 8 j a (by omega_using [b])
  have hK9 : VG.Proof.Poly1305.Arm.redK E 9 ≤ 2 ^ 13 := by
    have : 2 ^ 117 * VG.Proof.Poly1305.Arm.redK E 9 ≤ VG.Proof.Poly1305.Arm.val (VG.Proof.Poly1305.Arm.redK E) := by simp only [VG.Proof.Poly1305.Arm.val]; omega_using [h0, hK0]
    omega_using [hvl, hvK, this]
  have hK : ∀ j < 10, VG.Proof.Poly1305.Arm.redK E j ≤ 2 ^ 13 := fun j hj' => by
    rcases Nat.lt_or_ge j 9 with h | h
    · rcases Nat.lt_or_ge j 1 with h' | h'
      · rw [show j = 0 by omega_using [hj', h, h'], hK0]; omega_using [h0, hK0]
      · have := hKm j h' h; omega_using [this]
    · rw [show j = 9 by omega_using [hj', h]]; exact hK9
  have hc : VG.Proof.Poly1305.Arm.redC E ≤ 1 := by simp only [VG.Proof.Poly1305.Arm.redC]; omega_using [hvl, hvK]
  have hK' : ∀ j < 10, VG.Proof.Poly1305.Arm.redK' E j < 2 ^ 32 - 2 ^ 19 := fun j hj' => by
    have := hK j hj'
    simp only [VG.Proof.Poly1305.Arm.redK']; split <;> omega_using [h0, hK0, hc, this]
  have hl : ∀ j < 9, VG.Proof.Poly1305.Arm.carryN (VG.Proof.Poly1305.Arm.redK' E) 0 9 j < 2 ^ 13 := fun j hj' => VG.Proof.Poly1305.Arm.carryN_lt _ 0 9 j (by omega_using [hj']) (by omega_using [hj'])
  refine ⟨hH, hK, hK', ?_, fun j hj' => ?_⟩
  · have hm := VG.Proof.Poly1305.Arm.val_mask_top (g := VG.Proof.Poly1305.Arm.carryN (VG.Proof.Poly1305.Arm.redK' E) 0 9) (g' := VG.Proof.Poly1305.Arm.redL E) hl
      (fun k hk => by simp only [VG.Proof.Poly1305.Arm.redL]; rw [VG.Proof.Poly1305.Arm.iteF (by omega_using [hk])]) (by simp only [VG.Proof.Poly1305.Arm.redL, ↓reduceIte, Nat.reducePow])
    rw [hm, VG.Proof.Poly1305.Arm.val_carryN _ 0 9 (by decide)]
    have e : VG.Proof.Poly1305.Arm.val (VG.Proof.Poly1305.Arm.redK' E) = VG.Proof.Poly1305.Arm.val (VG.Proof.Poly1305.Arm.redK E) + 5 * VG.Proof.Poly1305.Arm.redC E := by
      simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, VG.Proof.Poly1305.Arm.val, VG.Proof.Poly1305.Arm.redK']; omega_using []
    rw [e, VG.Proof.Poly1305.Arm.redC, VG.Proof.Poly1305.Arm.reduce_eq (by omega_using [hvl, hvK, e]), hvK, hv]
  · simp only [VG.Proof.Poly1305.Arm.redL]
    split
    · exact Nat.mod_lt _ (by decide)
    · exact hl j (by omega)

/-! ## Clamping -/

theorem land_split32 {a b c d : Nat} (ha : a < 2 ^ 32) (hc : c < 2 ^ 32) :
    (a + 2 ^ 32 * b) &&& (c + 2 ^ 32 * d) = (a &&& c) + 2 ^ 32 * (b &&& d) := by
  apply Nat.eq_of_testBit_eq
  intro i
  have hac : (a &&& c) < 2 ^ 32 := Nat.lt_of_le_of_lt Nat.and_le_left ha
  rw [Nat.testBit_and]
  rw [Nat.add_comm a, Nat.add_comm c, Nat.add_comm (a &&& c)]
  rw [Nat.testBit_two_pow_mul_add _ ha, Nat.testBit_two_pow_mul_add _ hc,
    Nat.testBit_two_pow_mul_add _ hac]
  split <;> simp only [Nat.testBit_and]

/-- The clamped `r` of a key stored as four little-endian words. -/
theorem clamp_words {k0 k1 k2 k3 : Nat} (h0 : k0 < 2 ^ 32) (h1 : k1 < 2 ^ 32) (h2 : k2 < 2 ^ 32) :
    VG.Spec.Poly1305.clamp (k0 + 2 ^ 32 * k1 + 2 ^ 64 * k2 + 2 ^ 96 * k3) =
      (k0 &&& 0x0fffffff) + 2 ^ 32 * (k1 &&& 0x0ffffffc) + 2 ^ 64 * (k2 &&& 0x0ffffffc) +
        2 ^ 96 * (k3 &&& 0x0ffffffc) := by
  have e : ∀ x y z w : Nat, x + 2 ^ 32 * y + 2 ^ 64 * z + 2 ^ 96 * w =
      x + 2 ^ 32 * (y + 2 ^ 32 * (z + 2 ^ 32 * w)) := fun x y z w => by omega_using []
  rw [VG.Spec.Poly1305.clamp, e, e, show (0x0ffffffc0ffffffc0ffffffc0fffffff : Nat) =
    0x0fffffff + 2 ^ 32 * (0x0ffffffc + 2 ^ 32 * (0x0ffffffc + 2 ^ 32 * 0x0ffffffc)) from rfl,
    VG.Proof.Poly1305.Arm.land_split32 h0 (by decide), VG.Proof.Poly1305.Arm.land_split32 h1 (by decide), VG.Proof.Poly1305.Arm.land_split32 h2 (by decide)]

theorem and_lt {k m : Nat} (h : m < 2 ^ 28) : (k &&& m) < 2 ^ 28 :=
  Nat.lt_of_le_of_lt Nat.and_le_right h

theorem and_fffffffc_mod (k : Nat) : (k &&& 0x0ffffffc) % 2 = 0 := by
  rw [show (2 : Nat) = 2 ^ 1 from rfl, ← Nat.and_two_pow_sub_one_eq_mod, Nat.and_assoc,
    show (0x0ffffffc &&& 2 ^ 1 - 1 : Nat) = 0 by decide, Nat.and_zero]

end VG.Proof.Poly1305.Arm

end

/-!
# Poly1305 on 32-bit ARM: common lemmas

Facts about the registers the code uses, which registers a piece of code may
change (`Keeps`), and WP rules for one instruction at a time that expose only
what changes.
-/

namespace VG.Proof.Poly1305.Arm

open VG VG.Arm VG.Impl.Poly1305.Arm

/-! ## Registers -/

theorem yr_ne : ∀ k < 9, yr k ≠ .r0 ∧ yr k ≠ .r1 ∧ yr k ≠ .r2 ∧ yr k ≠ .r12 := by decide +kernel
theorem yr9 : yr 9 = .r1 := rfl
theorem yr_ne' : ∀ k < 10, yr k ≠ .r0 ∧ yr k ≠ .r2 ∧ yr k ≠ .r12 := by decide +kernel
theorem yr_inj : ∀ j < 10, ∀ k < 10, yr j = yr k → j = k := by decide +kernel
theorem xr_ne : ∀ k < 10, xr k ≠ .r0 ∧ xr k ≠ .r1 ∧ xr k ≠ .r2 := by decide +kernel
theorem xr_inj : ∀ j < 10, ∀ k < 10, xr j = xr k → j = k := by decide +kernel
theorem yr_eq_xr : ∀ k < 9, yr k = xr k := by decide +kernel
theorem xr9 : xr 9 = .r12 := rfl

/-- The registers `r1`–`r12`: every register the code changes but `r0` and `lr`. -/
def work : List Reg := [.r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12]

theorem yr_work : ∀ k < 10, yr k ∈ VG.Proof.Poly1305.Arm.work := by decide +kernel
theorem xr_work : ∀ k < 10, xr k ∈ VG.Proof.Poly1305.Arm.work := by decide +kernel

/-! ## What code changes -/

/-- `s'` is `s` except for the registers `ws` and the flags. -/
structure Keeps (ws : List Reg) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ ws → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Keeps.refl (ws : List Reg) (s : State) : VG.Proof.Poly1305.Arm.Keeps ws s s :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem Keeps.trans {ws : List Reg} {s₁ s₂ s₃ : State} (h₁ : VG.Proof.Poly1305.Arm.Keeps ws s₁ s₂) (h₂ : VG.Proof.Poly1305.Arm.Keeps ws s₂ s₃) :
    VG.Proof.Poly1305.Arm.Keeps ws s₁ s₃ :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd,
    h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp⟩

theorem Keeps.mono {ws ws' : List Reg} {s s' : State} (h : VG.Proof.Poly1305.Arm.Keeps ws s s') (hs : ∀ r ∈ ws, r ∈ ws') :
    VG.Proof.Poly1305.Arm.Keeps ws' s s' :=
  ⟨fun r hr => h.gpr r fun h' => hr (hs r h'), h.mem, h.rd, h.wr, h.sp⟩

/-! ## One instruction at a time -/

/-- `s'` is `s` with register `d` set to `v` (the flags aside). -/
structure Upd (s s' : State) (d : Reg) (v : BitVec 32) : Prop where
  gpr : s'.gpr d = v
  other : ∀ r, r ≠ d → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Upd.setReg (s : State) (d : Reg) (v : BitVec 32) : VG.Proof.Poly1305.Arm.Upd s (s.setReg d v) d v :=
  ⟨by simp only [State.setReg, ↓reduceIte], fun r h => by simp only [State.setReg, h, ↓reduceIte], rfl, rfl, rfl, rfl⟩

theorem Upd.subs (s : State) (d : Reg) (x y v : BitVec 32) : VG.Proof.Poly1305.Arm.Upd s ((subFlags s x y).setReg d v) d v :=
  ⟨by simp only [State.setReg, ↓reduceIte], fun r h => by simp only [State.setReg, subFlags, BitVec.ofNat_eq_ofNat, h, ↓reduceIte], rfl, rfl, rfl, rfl⟩

theorem Upd.keeps {s s' : State} {d : Reg} {v : BitVec 32} (h : VG.Proof.Poly1305.Arm.Upd s s' d v) {ws : List Reg}
    (hd : d ∈ ws) : VG.Proof.Poly1305.Arm.Keeps ws s s' :=
  ⟨fun r hr => h.other r fun e => hr (e ▸ hd), h.mem, h.rd, h.wr, h.sp⟩

/-- `s'` is `s` with memory `m`. -/
structure Mupd (s s' : State) (m : Mem) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = m
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  z : s'.z = s.z

/-- `s'` is `s` with other flags. -/
structure Fupd (s s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

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

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_mov {d : Reg} {o : Op2} {v : BitVec 32} (ho : o.eval s = some v)
    (k : ∀ s', VG.Proof.Poly1305.Arm.Upd s s' d v → WP isa (.block is) s' Q) : WP isa (.block (.mov d o :: is)) s Q :=
  WP.cons (s' := s.setReg d v) (by simp only [exec, ho, Option.map_some]) (k _ (Upd.setReg _ _ _))

theorem wp_add {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', VG.Proof.Poly1305.Arm.Upd s s' d (s.gpr n + y) → WP isa (.block is) s' Q) :
    WP isa (.block (.dp .add d n o :: is)) s Q :=
  WP.cons (s' := s.setReg d (s.gpr n + y)) (by simp only [exec, ho, Option.map_some]) (k _ (Upd.setReg _ _ _))

theorem wp_and {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', VG.Proof.Poly1305.Arm.Upd s s' d (s.gpr n &&& y) → WP isa (.block is) s' Q) :
    WP isa (.block (.dp .and d n o :: is)) s Q :=
  WP.cons (s' := s.setReg d (s.gpr n &&& y)) (by simp only [exec, ho, Option.map_some]) (k _ (Upd.setReg _ _ _))

theorem wp_mul {d n m : Reg} (k : ∀ s', VG.Proof.Poly1305.Arm.Upd s s' d (s.gpr n * s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.mul d n m :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

theorem wp_movw {d : Reg} {imm : BitVec 16}
    (k : ∀ s', VG.Proof.Poly1305.Arm.Upd s s' d (imm.setWidth 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movw d imm :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

theorem wp_movt {d : Reg} {imm : BitVec 16}
    (k : ∀ s', VG.Proof.Poly1305.Arm.Upd s s' d (imm ++ (s.gpr d).extractLsb' 0 16 : BitVec 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movt d imm :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

theorem wp_subs {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', VG.Proof.Poly1305.Arm.Upd s s' d (s.gpr n - y) → s'.z = (s.gpr n - y == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.subs d n o :: is)) s Q :=
  WP.cons (s' := (subFlags s (s.gpr n) y).setReg d (s.gpr n - y)) (by simp only [exec, ho, Option.map_some])
    (k _ (Upd.subs _ _ _ _ _) rfl)

theorem wp_cmp {n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', VG.Proof.Poly1305.Arm.Fupd s s' → s'.z = (s.gpr n - y == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.cmp n o :: is)) s Q :=
  WP.cons (s' := subFlags s (s.gpr n) y) (by simp only [exec, ho, Option.map_some]) (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl)

theorem wp_ldr {t n : Reg} {off : Nat} {a : Addr} (ho : off < 4096)
    (ha : State.addr (s.gpr n + BitVec.ofNat 32 off) = a) (hin : InRegions (s.rd ++ s.wr) a 4)
    (k : ∀ s', VG.Proof.Poly1305.Arm.Upd s s' t (s.mem.readW a 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldr t n off :: is)) s Q := by
  subst ha
  exact WP.cons (exec_ldr ho hin) (k _ (Upd.setReg _ _ _))

theorem wp_str {t n : Reg} {off : Nat} {a : Addr} (ho : off < 4096)
    (ha : State.addr (s.gpr n + BitVec.ofNat 32 off) = a) (hout : InRegions s.wr a 4)
    (k : ∀ s', VG.Proof.Poly1305.Arm.Mupd s s' (s.mem.writeW a (s.gpr t)) → WP isa (.block is) s' Q) :
    WP isa (.block (.str t n off :: is)) s Q := by
  subst ha
  exact WP.cons (exec_str ho hout) (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)

theorem wp_ldrb {t n : Reg} {off : Nat} {a : Addr} (ho : off < 4096)
    (ha : State.addr (s.gpr n + BitVec.ofNat 32 off) = a) (hin : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ s', VG.Proof.Poly1305.Arm.Upd s s' t ((s.mem a).setWidth 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldrb t n off :: is)) s Q := by
  subst ha
  exact WP.cons (s' := s.setReg t ((s.mem _).setWidth 32)) (by simp only [exec, ho, ↓reduceIte, State.load8, hin, Option.map_some])
    (k _ (Upd.setReg _ _ _))

theorem wp_strb {t n : Reg} {off : Nat} {a : Addr} (ho : off < 4096)
    (ha : State.addr (s.gpr n + BitVec.ofNat 32 off) = a) (hout : InRegions s.wr a 1)
    (k : ∀ s', VG.Proof.Poly1305.Arm.Mupd s s' (s.mem.writeW a ((s.gpr t).setWidth 8)) → WP isa (.block is) s' Q) :
    WP isa (.block (.strb t n off :: is)) s Q := by
  subst ha
  exact WP.cons (s' := { s with mem := s.mem.writeW _ ((s.gpr t).setWidth 8) })
    (by simp only [exec, ho, ↓reduceIte, State.store8, hout]) (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)

end

/-- Running `l ++ rest` by running `l` first. -/
theorem WP.append {l rest : List Instr} {s : State} {P Q : State → Prop}
    (h : WP isa (.block l) s P) (k : ∀ s', P s' → WP isa (.block rest) s' Q) :
    WP isa (.block (l ++ rest)) s Q :=
  WP.block_append_iff.mpr (WP.mono h k)

/-! ## 32-bit arithmetic -/

theorem toNat_add_lt {x y : BitVec 32} (h : x.toNat + y.toNat < 2 ^ 32) :
    (x + y).toNat = x.toNat + y.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]

theorem toNat_mul_lt {x y : BitVec 32} (h : x.toNat * y.toNat < 2 ^ 32) :
    (x * y).toNat = x.toNat * y.toNat := by
  rw [BitVec.toNat_mul, Nat.mod_eq_of_lt h]

theorem toNat_shr (x : BitVec 32) (n : Nat) : (x >>> n).toNat = x.toNat / 2 ^ n := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem toNat_shl (x : BitVec 32) (n : Nat) : (x <<< n).toNat = x.toNat * 2 ^ n % 2 ^ 32 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

theorem toNat_and_mask (x : BitVec 32) : (x &&& (0x1fff#16).setWidth 32).toNat = x.toNat % 2 ^ 13 := by
  rw [BitVec.toNat_and, show ((0x1fff#16).setWidth 32).toNat = 2 ^ 13 - 1 by rfl,
    Nat.and_two_pow_sub_one_eq_mod]

/-! ## Addresses -/

theorem contains_off {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n := Offset.contains_base base h ho

theorem off_sep (p : Addr) {d e n k : Nat} (hd : d < 2 ^ 32) (he : e < 2 ^ 32) (hn : n ≤ 8)
    (hk : k ≤ 8) (h : d + n ≤ e ∨ e + k ≤ d) :
    Mem.Sep (p + BitVec.ofNat 64 d) n (p + BitVec.ofNat 64 e) k := Offset.sep p h (by omega_using [hd, hn]) (by omega_using [he, hk])

/-- Reading a word after writing one elsewhere. -/
theorem readW_writeW_off (m : Mem) (p : Addr) (v : BitVec 32) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (p + BitVec.ofNat 64 e) v).readW (p + BitVec.ofNat 64 d) 32 =
      m.readW (p + BitVec.ofNat 64 d) 32 :=
  Mem.readW_writeW_sep (VG.Proof.Poly1305.Arm.off_sep p hd he (by decide) (by decide) h) (by decide)

theorem contains_sub (p : Addr) {a len d n : Nat} (h1 : a ≤ d) (h2 : d + n ≤ a + len)
    (h3 : a + len < 2 ^ 32) :
    (⟨p + BitVec.ofNat 64 a, len⟩ : Region).Contains (p + BitVec.ofNat 64 d) n := Offset.contains p h1 h2 (by omega_using [h3])

theorem disjoint_sub (p : Addr) {a la b lb : Nat} (h : a + la ≤ b ∨ b + lb ≤ a)
    (ha : a + la < 2 ^ 32) (hb : b + lb < 2 ^ 32) :
    (⟨p + BitVec.ofNat 64 a, la⟩ : Region).Disjoint ⟨p + BitVec.ofNat 64 b, lb⟩ := Offset.disjoint p h (by omega_using [ha]) (by omega_using [hb])

theorem sub_sub (p : Addr) {a len b len' : Nat} (h1 : b ≤ a) (h2 : a + len ≤ b + len')
    (_h3 : b + len' < 2 ^ 32) :
    Region.Sub ⟨p + BitVec.ofNat 64 a, len⟩ ⟨p + BitVec.ofNat 64 b, len'⟩ := Offset.sub p h1 h2

/-! ## The state -/

/-- The state's region. -/
abbrev stR (st : BitVec 32) : Region := ⟨State.addr st, 128⟩

theorem ea {st : BitVec 32} (hfit : st.toNat + 128 ≤ 2 ^ 32) {off : Nat} (h : off < 128) :
    State.addr (st + BitVec.ofNat 32 off) = State.addr st + BitVec.ofNat 64 off :=
  addr_add (by omega_using [hfit, h])

theorem inSt {st : BitVec 32} {s : State} (hw : VG.Proof.Poly1305.Arm.stR st ∈ s.wr) {off n : Nat} (h : off + n ≤ 128) :
    InRegions (s.rd ++ s.wr) (State.addr st + BitVec.ofNat 64 off) n :=
  ⟨_, List.mem_append_right _ hw, VG.Proof.Poly1305.Arm.contains_off h (by omega_using [h])⟩

theorem outSt {st : BitVec 32} {s : State} (hw : VG.Proof.Poly1305.Arm.stR st ∈ s.wr) {off n : Nat} (h : off + n ≤ 128) :
    InRegions s.wr (State.addr st + BitVec.ofNat 64 off) n :=
  ⟨_, hw, VG.Proof.Poly1305.Arm.contains_off h (by omega_using [h])⟩

end VG.Proof.Poly1305.Arm

end

-- Formerly the module `VerifiedGarbage.Proof.Poly1305.Arm.Reduce`.
section

section

/-!
# Poly1305 on 32-bit ARM: adding the limbs of four words to the columns

`addWords` adds limbs 0–8 of the 16 bytes at `r1` to `r3`–`r11`, piece by
piece (`piece_ok`), and leaves the last word in `r2` (`addWords_ok`); as
numbers, the limbs are `mlimb`.
-/

namespace VG.Proof.Poly1305.Arm

open VG VG.Arm VG.Impl.Poly1305.Arm

/-- What piece `p` of the word `w` adds to its column. -/
def pieceBV (w : BitVec 32) : Nat × Nat × Nat → BitVec 32
  | (_, 0, b) => w >>> b
  | (_, a, b) => (w <<< a) >>> b

/-- What the pieces `l` of the word `w` add to column `k`. -/
def contrib : List (Nat × Nat × Nat) → Nat → BitVec 32 → BitVec 32
  | [], _, _ => 0
  | p :: ps, k, w => (if p.1 = k then VG.Proof.Poly1305.Arm.pieceBV w p else 0) + VG.Proof.Poly1305.Arm.contrib ps k w

/-- The columns' registers. -/
def yregs : List Reg := [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11]

theorem yr_yregs : ∀ k < 9, yr k ∈ VG.Proof.Poly1305.Arm.yregs := by decide +kernel

theorem zadd (x : BitVec 32) : 0 + x = x := by simp only [BitVec.ofNat_eq_ofNat, BitVec.zero_add]
theorem addz (x : BitVec 32) : x + 0 = x := by simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero]

theorem piece_ok (p : Nat × Nat × Nat) (hk : p.1 < 9) (ha : p.2.1 ≤ 31) (hb : 1 ≤ p.2.2 ∧ p.2.2 ≤ 31)
    {rest : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', s'.gpr (yr p.1) = s.gpr (yr p.1) + VG.Proof.Poly1305.Arm.pieceBV (s.gpr .r2) p →
      VG.Proof.Poly1305.Arm.Keeps [yr p.1, .r12] s s' → WP isa (.block rest) s' Q) :
    WP isa (.block (piece p ++ rest)) s Q := by
  obtain ⟨c, a, b⟩ := p
  simp only at hk ha hb k
  have hne := VG.Proof.Poly1305.Arm.yr_ne c hk
  cases a with
  | zero =>
    simp only [piece, List.cons_append, List.nil_append]
    exact VG.Proof.Poly1305.Arm.wp_add (VG.Proof.Poly1305.Arm.op2_lsr hb) fun s1 u1 => k s1 u1.gpr (u1.keeps (by simp only [List.mem_cons, List.not_mem_nil, or_false, true_or]))
  | succ a =>
    simp only [piece, List.cons_append, List.nil_append]
    refine VG.Proof.Poly1305.Arm.wp_mov (VG.Proof.Poly1305.Arm.op2_lsl ⟨by omega_using [ha], ha⟩) fun s1 u1 => VG.Proof.Poly1305.Arm.wp_add (VG.Proof.Poly1305.Arm.op2_lsr hb) fun s2 u2 => ?_
    refine k s2 ?_ ((u1.keeps (by simp only [List.mem_cons, List.not_mem_nil, or_false, or_true])).trans (u2.keeps (by simp only [List.mem_cons, List.not_mem_nil, or_false, true_or])))
    rw [u2.gpr, u1.gpr, u1.other _ hne.2.2.2]
    rfl

theorem pieces_ok (l : List (Nat × Nat × Nat))
    (hl : ∀ p ∈ l, p.1 < 9 ∧ p.2.1 ≤ 31 ∧ 1 ≤ p.2.2 ∧ p.2.2 ≤ 31)
    {rest : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', (∀ j < 9, s'.gpr (yr j) = s.gpr (yr j) + VG.Proof.Poly1305.Arm.contrib l j (s.gpr .r2)) →
      VG.Proof.Poly1305.Arm.Keeps (.r12 :: VG.Proof.Poly1305.Arm.yregs) s s' → WP isa (.block rest) s' Q) :
    WP isa (.block (l.flatMap piece ++ rest)) s Q := by
  induction l generalizing s with
  | nil => exact k s (fun j _ => by simp only [VG.Proof.Poly1305.Arm.contrib, BitVec.ofNat_eq_ofNat, BitVec.add_zero]) (Keeps.refl _ _)
  | cons p ps ih =>
    have hp := hl p List.mem_cons_self
    rw [List.flatMap_cons, List.append_assoc]
    refine VG.Proof.Poly1305.Arm.piece_ok p hp.1 hp.2.1 hp.2.2 fun s1 h1 k1 => ?_
    refine ih (fun q hq => hl q (List.mem_cons_of_mem _ hq)) fun s2 h2 k2 => k s2 (fun j hj => ?_) ?_
    · have e2 : s1.gpr .r2 = s.gpr .r2 := k1.gpr _ (by have := VG.Proof.Poly1305.Arm.yr_ne p.1 hp.1; simp only [List.mem_cons, this.2.2.1.symm, reduceCtorEq, List.not_mem_nil, or_self, not_false_eq_true])
      rw [h2 j hj, e2, VG.Proof.Poly1305.Arm.contrib]
      by_cases e : p.1 = j
      · subst e; rw [h1]; simp only [ite_true, BitVec.add_assoc]
      · have e1 : s1.gpr (yr j) = s.gpr (yr j) := k1.gpr _ (by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨fun h => e (VG.Proof.Poly1305.Arm.yr_inj _ (by omega_using [hj]) _ (by omega_using [hp]) h).symm, (VG.Proof.Poly1305.Arm.yr_ne j hj).2.2.2⟩)
        rw [e1]; simp only [e, ite_false, VG.Proof.Poly1305.Arm.zadd]
    · exact (k1.mono fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact List.mem_cons_of_mem _ (VG.Proof.Poly1305.Arm.yr_yregs _ hp.1)
        · exact List.mem_cons_self).trans k2

theorem pieces_valid : ∀ i < 4, ∀ p ∈ pieces i, p.1 < 9 ∧ p.2.1 ≤ 31 ∧ 1 ≤ p.2.2 ∧ p.2.2 ≤ 31 := by
  decide

/-- The words at `r1`. -/
def word (s : State) (i : Nat) : BitVec 32 :=
  s.mem.readW (State.addr (s.gpr .r1 + BitVec.ofNat 32 (4 * i))) 32

/-- What words `0, …, i - 1` add to column `k`. -/
def wsum (w : Nat → BitVec 32) : Nat → Nat → BitVec 32
  | 0, _ => 0
  | i + 1, k => VG.Proof.Poly1305.Arm.wsum w i k + VG.Proof.Poly1305.Arm.contrib (pieces i) k (w i)

/-- After words `< i` (the registers relative to `s₀`). -/
structure WI (s₀ : State) (i : Nat) (s : State) : Prop where
  cols : ∀ j < 9, s.gpr (yr j) = s₀.gpr (yr j) + VG.Proof.Poly1305.Arm.wsum (VG.Proof.Poly1305.Arm.word s₀) i j
  r2 : 0 < i → s.gpr .r2 = VG.Proof.Poly1305.Arm.word s₀ (i - 1)
  keeps : VG.Proof.Poly1305.Arm.Keeps (.r2 :: .r12 :: VG.Proof.Poly1305.Arm.yregs) s₀ s

theorem addWord_step {s₀ : State}
    (hin : ∀ i < 4, InRegions (s₀.rd ++ s₀.wr) (State.addr (s₀.gpr .r1 + BitVec.ofNat 32 (4 * i))) 4)
    (i : Nat) (s : State) (hi : i < 4) (h : VG.Proof.Poly1305.Arm.WI s₀ i s) : WP isa (.block (addWord i)) s (VG.Proof.Poly1305.Arm.WI s₀ (i + 1)) := by
  have e1 : s.gpr .r1 = s₀.gpr .r1 := h.keeps.gpr _ (by decide)
  rw [addWord, ← List.append_nil ((pieces i).flatMap piece)]
  refine VG.Proof.Poly1305.Arm.wp_ldr (by omega_using [hi]) rfl (by rw [e1, h.keeps.rd, h.keeps.wr]; exact hin i hi) fun s1 u1 => ?_
  have hw : s1.gpr .r2 = VG.Proof.Poly1305.Arm.word s₀ i := by rw [u1.gpr, e1, h.keeps.mem]; rfl
  refine VG.Proof.Poly1305.Arm.pieces_ok _ (VG.Proof.Poly1305.Arm.pieces_valid i hi) fun s2 h2 k2 => WP.block_nil ⟨fun j hj => ?_, fun _ => ?_, ?_⟩
  · rw [h2 j hj, hw, u1.other _ (VG.Proof.Poly1305.Arm.yr_ne j hj).2.2.1, h.cols j hj, VG.Proof.Poly1305.Arm.wsum, BitVec.add_assoc]
  · rw [k2.gpr _ (by decide), hw]; rfl
  · exact h.keeps.trans ((u1.keeps (by simp only [List.mem_cons, reduceCtorEq, false_or, true_or])).trans (k2.mono fun r hr => List.mem_cons_of_mem _ hr))

theorem addWords_ok {s₀ : State}
    (hin : ∀ i < 4, InRegions (s₀.rd ++ s₀.wr) (State.addr (s₀.gpr .r1 + BitVec.ofNat 32 (4 * i))) 4) :
    WP isa (.block addWords) s₀ fun s =>
      (∀ j < 9, s.gpr (yr j) = s₀.gpr (yr j) + VG.Proof.Poly1305.Arm.wsum (VG.Proof.Poly1305.Arm.word s₀) 4 j) ∧ s.gpr .r2 = VG.Proof.Poly1305.Arm.word s₀ 3 ∧
      VG.Proof.Poly1305.Arm.Keeps (.r2 :: .r12 :: VG.Proof.Poly1305.Arm.yregs) s₀ s := by
  refine WP.mono (wp_range_flatMap (M := isa) (VG.Proof.Poly1305.Arm.WI s₀) (VG.Proof.Poly1305.Arm.addWord_step hin) 4 (Nat.le_refl _) s₀
    ⟨fun j _ => by simp only [VG.Proof.Poly1305.Arm.wsum, BitVec.ofNat_eq_ofNat, BitVec.add_zero], fun h => absurd h (by decide), Keeps.refl _ _⟩)
    fun s h => ⟨h.cols, h.r2 (by decide), h.keeps⟩

/-! ## The limbs as numbers -/

/-- The limbs `addWords` adds, as numbers. -/
theorem shl_mod (Y a : Nat) (ha : a ≤ 32) : Y * 2 ^ a % 2 ^ 32 = 2 ^ a * (Y % 2 ^ (32 - a)) := by
  rw [show (2 : Nat) ^ 32 = 2 ^ (32 - a) * 2 ^ a by rw [← Nat.pow_add, Nat.sub_add_cancel ha],
    Nat.mul_mod_mul_right, Nat.mul_comm]

/-- `X + 2ᵃ Y` fits `n` bits. -/
theorem fits {X Y a c n : Nat} (hx : X < 2 ^ a) (hy : Y < 2 ^ c) (h : a + c ≤ n) :
    X + 2 ^ a * Y < 2 ^ n := by
  have h1 : 2 ^ a * Y + 2 ^ a ≤ 2 ^ a * 2 ^ c := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hy
  have h2 : 2 ^ a * 2 ^ c ≤ 2 ^ n := by rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) h
  omega_using [hx, h1, h2]

theorem modlt {Y c k : Nat} (hy : Y < 2 ^ c) : Y % 2 ^ k < 2 ^ c :=
  Nat.lt_of_le_of_lt (Nat.mod_le _ _) hy

theorem modw {Y c k : Nat} (hy : Y < 2 ^ c) (h : 2 ^ c ≤ 2 ^ k) : Y % 2 ^ k = Y :=
  Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hy h)

theorem shl_shr_le (x : BitVec 32) {a b : Nat} (h : a ≤ b) (ha : a ≤ 32) :
    ((x <<< a) >>> b).toNat = x.toNat % 2 ^ (32 - a) / 2 ^ (b - a) := by
  rw [VG.Proof.Poly1305.Arm.toNat_shr, VG.Proof.Poly1305.Arm.toNat_shl, VG.Proof.Poly1305.Arm.shl_mod _ _ ha,
    show (2 : Nat) ^ b = 2 ^ a * 2 ^ (b - a) by rw [← Nat.pow_add, Nat.add_sub_cancel' h],
    Nat.mul_div_mul_left _ _ (Nat.two_pow_pos _)]

theorem shl_shr_ge (x : BitVec 32) {a b : Nat} (h : b ≤ a) (ha : a ≤ 32) :
    ((x <<< a) >>> b).toNat = x.toNat % 2 ^ (32 - a) * 2 ^ (a - b) := by
  rw [VG.Proof.Poly1305.Arm.toNat_shr, VG.Proof.Poly1305.Arm.toNat_shl, VG.Proof.Poly1305.Arm.shl_mod _ _ ha,
    show (2 : Nat) ^ a = 2 ^ b * 2 ^ (a - b) by rw [← Nat.pow_add, Nat.add_sub_cancel' h],
    Nat.mul_assoc, Nat.mul_div_cancel_left _ (Nat.two_pow_pos _), Nat.mul_comm]

theorem add_piece (x y : BitVec 32) {a b c : Nat} (hba : b ≤ a) (ha : a ≤ 32) (hc : 32 - c = a - b)
    (hc' : c ≤ 32) :
    (x >>> c + (y <<< a) >>> b).toNat = x.toNat / 2 ^ c + y.toNat % 2 ^ (32 - a) * 2 ^ (a - b) := by
  rw [BitVec.toNat_add, VG.Proof.Poly1305.Arm.toNat_shr, VG.Proof.Poly1305.Arm.shl_shr_ge _ hba ha]
  apply Nat.mod_eq_of_lt
  have h1 : x.toNat / 2 ^ c < 2 ^ (a - b) := by
    rw [← hc]; apply Nat.div_lt_of_lt_mul
    rw [← Nat.pow_add, Nat.add_sub_cancel' hc']; exact x.isLt
  have := VG.Proof.Poly1305.Arm.fits h1 (Nat.mod_lt y.toNat (Nat.two_pow_pos (32 - a))) (show a - b + (32 - a) ≤ 32 by omega_using [hba, ha])
  rwa [Nat.mul_comm] at this

set_option linter.unusedSimpArgs false in
theorem wsum_toNat (w : Nat → BitVec 32) {k : Nat} (hk : k < 9) :
    (VG.Proof.Poly1305.Arm.wsum w 4 k).toNat = VG.Proof.Poly1305.Arm.mlimb (w 0).toNat (w 1).toNat (w 2).toNat (w 3).toNat k := by
  simp only [VG.Proof.Poly1305.Arm.wsum, VG.Proof.Poly1305.Arm.contrib, pieces, VG.Proof.Poly1305.Arm.pieceBV, VG.Proof.Poly1305.Arm.zadd, VG.Proof.Poly1305.Arm.addz]
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
    k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 := by omega
  all_goals simp only [VG.Proof.Poly1305.Arm.mlimb, Nat.reduceEqDiff, ite_true, ite_false, VG.Proof.Poly1305.Arm.zadd, VG.Proof.Poly1305.Arm.addz, VG.Proof.Poly1305.Arm.toNat_shr,
    VG.Proof.Poly1305.Arm.shl_shr_le _ (show 19 ≤ 19 by decide) (by decide), VG.Proof.Poly1305.Arm.shl_shr_le _ (show 6 ≤ 19 by decide) (by decide),
    VG.Proof.Poly1305.Arm.shl_shr_le _ (show 12 ≤ 19 by decide) (by decide), VG.Proof.Poly1305.Arm.shl_shr_le _ (show 18 ≤ 19 by decide) (by decide),
    VG.Proof.Poly1305.Arm.shl_shr_le _ (show 5 ≤ 19 by decide) (by decide), VG.Proof.Poly1305.Arm.shl_shr_le _ (show 11 ≤ 19 by decide) (by decide),
    VG.Proof.Poly1305.Arm.shl_shr_ge _ (show 19 ≤ 25 by decide) (by decide), VG.Proof.Poly1305.Arm.shl_shr_ge _ (show 19 ≤ 31 by decide) (by decide),
    VG.Proof.Poly1305.Arm.shl_shr_ge _ (show 19 ≤ 24 by decide) (by decide), Nat.reduceSub]
  all_goals first
    | exact Nat.div_one _
    | exact (VG.Proof.Poly1305.Arm.add_piece _ _ (by decide) (by decide) (by decide) (by decide)).trans rfl

end VG.Proof.Poly1305.Arm

end

section

/-!
# Poly1305 on 32-bit ARM: carrying and the final reduction

The columns (or limbs) are in `r3`–`r11` and `r1` (`Cols`); `carryStep` moves
a column's bits from 13 up to the next column (`carries_ok`), `carryFold`
carries them all into `fold` (`carryFold_ok`), and `reduce` reduces them fully
(`reduceRegs_ok`).
-/

namespace VG.Proof.Poly1305.Arm

open VG VG.Arm VG.Impl.Poly1305.Arm

/-- The columns (or limbs) are `v`, in `r3`–`r11` and `r1`. -/
def Cols (v : Nat → Nat) (s : State) : Prop := ∀ j < 10, (s.gpr (yr j)).toNat = v j

/-- The mask `movw r2, #0x1fff` leaves in `r2`. -/
abbrev maskV : BitVec 32 := (0x1fff#16).setWidth 32

/-- The registers of the columns. -/
def cregs : List Reg := .r1 :: VG.Proof.Poly1305.Arm.yregs

theorem yr_cregs : ∀ k < 10, yr k ∈ VG.Proof.Poly1305.Arm.cregs := by decide +kernel

theorem cregs_r2 : Reg.r2 ∉ VG.Proof.Poly1305.Arm.cregs := by decide
theorem cregs_r12 : Reg.r12 ∉ VG.Proof.Poly1305.Arm.cregs := by decide
theorem cregs_r0 : Reg.r0 ∉ VG.Proof.Poly1305.Arm.cregs := by decide

theorem carryStep_ok {k : Nat} (hk : k < 9) {s : State} (hm : s.gpr .r2 = VG.Proof.Poly1305.Arm.maskV)
    (hb : (s.gpr (yr (k + 1))).toNat + (s.gpr (yr k)).toNat / 2 ^ 13 < 2 ^ 32) :
    WP isa (.block (carryStep k)) s fun s' =>
      (s'.gpr (yr (k + 1))).toNat = (s.gpr (yr (k + 1))).toNat + (s.gpr (yr k)).toNat / 2 ^ 13 ∧
      (s'.gpr (yr k)).toNat = (s.gpr (yr k)).toNat % 2 ^ 13 ∧ VG.Proof.Poly1305.Arm.Keeps [yr k, yr (k + 1)] s s' := by
  have hne : yr k ≠ yr (k + 1) := fun h => absurd (VG.Proof.Poly1305.Arm.yr_inj _ (by omega_using [hk]) _ (by omega_using [hk]) h) (by omega_using [])
  have h2 : yr k ≠ .r2 := (VG.Proof.Poly1305.Arm.yr_ne k hk).2.2.1
  refine VG.Proof.Poly1305.Arm.wp_add (VG.Proof.Poly1305.Arm.op2_lsr (by decide)) fun s1 u1 => VG.Proof.Poly1305.Arm.wp_and (VG.Proof.Poly1305.Arm.op2_reg _ _) fun s2 u2 => WP.block_nil ?_
  refine ⟨?_, ?_, (u1.keeps (by simp only [List.mem_cons, List.not_mem_nil, or_false, or_true])).trans (u2.keeps (by simp only [List.mem_cons, List.not_mem_nil, or_false, true_or]))⟩
  · rw [u2.other _ hne.symm, u1.gpr, VG.Proof.Poly1305.Arm.toNat_add_lt (by rw [VG.Proof.Poly1305.Arm.toNat_shr]; exact hb), VG.Proof.Poly1305.Arm.toNat_shr]
  · rw [u2.gpr, u1.other _ hne, u1.other _ (Ne.symm (VG.Proof.Poly1305.Arm.yr_ne' (k + 1) (by omega_using [hk])).2.1), hm, VG.Proof.Poly1305.Arm.toNat_and_mask]

/-- After the carries from columns `a`, …, `a + k - 1`. -/
structure CI (f : Nat → Nat) (a : Nat) (s₀ : State) (k : Nat) (s : State) : Prop where
  cols : VG.Proof.Poly1305.Arm.Cols (VG.Proof.Poly1305.Arm.carryN f a k) s
  keeps : VG.Proof.Poly1305.Arm.Keeps VG.Proof.Poly1305.Arm.cregs s₀ s

theorem carries_ok (a n : Nat) (hn : n + a ≤ 9) {f : Nat → Nat} (hf : ∀ j < 10, f j < 2 ^ 32 - 2 ^ 19)
    {s : State} (hc : VG.Proof.Poly1305.Arm.Cols f s) (hm : s.gpr .r2 = VG.Proof.Poly1305.Arm.maskV) :
    WP isa (.block ((List.range n).flatMap fun k => carryStep (k + a))) s fun s' =>
      VG.Proof.Poly1305.Arm.Cols (VG.Proof.Poly1305.Arm.carryN f a n) s' ∧ VG.Proof.Poly1305.Arm.Keeps VG.Proof.Poly1305.Arm.cregs s s' := by
  refine WP.mono (wp_range_flatMap (M := isa) (VG.Proof.Poly1305.Arm.CI f a s) (fun k s' hk h => ?_) n (Nat.le_refl _) s
    ⟨hc, Keeps.refl _ _⟩) fun s' h => ⟨h.cols, h.keeps⟩
  have hm' : s'.gpr .r2 = VG.Proof.Poly1305.Arm.maskV := by rw [h.keeps.gpr _ VG.Proof.Poly1305.Arm.cregs_r2, hm]
  have hb := VG.Proof.Poly1305.Arm.carryN_step_lt f a hf k (by omega_using [hn, hk])
  refine WP.mono (VG.Proof.Poly1305.Arm.carryStep_ok (k := k + a) (by omega_using [hn, hk]) hm' (by
    rw [h.cols _ (by omega_using [hn, hk]), h.cols _ (by omega_using [hn, hk])]; exact hb)) fun s'' ⟨e1, e0, hk⟩ => ⟨?_, ?_⟩
  · intro j hj
    simp only [VG.Proof.Poly1305.Arm.carryN, VG.Proof.Poly1305.Arm.cstep]
    by_cases ej : j = k + a
    · subst ej; rw [VG.Proof.Poly1305.Arm.iteT rfl, e0, h.cols _ hj]
    by_cases ej' : j = k + a + 1
    · subst ej'; rw [VG.Proof.Poly1305.Arm.iteF ej, VG.Proof.Poly1305.Arm.iteT rfl, e1, h.cols _ hj, h.cols _ (by omega_using [hj])]
    · rw [VG.Proof.Poly1305.Arm.iteF ej, VG.Proof.Poly1305.Arm.iteF ej', hk.gpr _ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨fun e => ej (VG.Proof.Poly1305.Arm.yr_inj _ hj _ (by omega) e), fun e => ej' (VG.Proof.Poly1305.Arm.yr_inj _ hj _ (by omega) e)⟩),
        h.cols _ hj]
  · exact h.keeps.trans (hk.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact VG.Proof.Poly1305.Arm.yr_cregs _ (by omega))

end VG.Proof.Poly1305.Arm

end

/-!
# Poly1305 on 32-bit ARM: carrying all columns, the final reduction, and words
-/

namespace VG.Proof.Poly1305.Arm

open VG VG.Arm VG.Impl.Poly1305.Arm

theorem Cols.keep {v : Nat → Nat} {s s' : State} (h : VG.Proof.Poly1305.Arm.Cols v s) {ws : List Reg} (hk : VG.Proof.Poly1305.Arm.Keeps ws s s')
    (hw : ∀ j < 10, yr j ∉ ws) : VG.Proof.Poly1305.Arm.Cols v s' := fun j hj => by rw [hk.gpr _ (hw j hj)]; exact h j hj

theorem carryFold_ok {f : Nat → Nat} (hf : ∀ j < 10, f j < 2 ^ 32 - 2 ^ 19) {s : State} (hc : VG.Proof.Poly1305.Arm.Cols f s) :
    WP isa (.block carryFold) s fun s' =>
      VG.Proof.Poly1305.Arm.Cols (VG.Proof.Poly1305.Arm.fold f) s' ∧ s'.gpr .r2 = VG.Proof.Poly1305.Arm.maskV ∧ VG.Proof.Poly1305.Arm.Keeps (.r2 :: .r12 :: VG.Proof.Poly1305.Arm.cregs) s s' := by
  rw [carryFold, List.cons_append, List.cons_append]
  refine VG.Proof.Poly1305.Arm.wp_movw fun s1 u1 => ?_
  have hc1 : VG.Proof.Poly1305.Arm.Cols f s1 := hc.keep (u1.keeps (List.mem_singleton_self _)) fun j hj => by
    simpa using (VG.Proof.Poly1305.Arm.yr_ne' j hj).2.1
  rw [List.append_assoc]
  refine WP.append (VG.Proof.Poly1305.Arm.carries_ok 0 9 (by decide) hf hc1 u1.gpr) fun s2 ⟨hc2, k2⟩ => ?_
  have hl := fun j (hj : j < 9) => VG.Proof.Poly1305.Arm.carryN_lt f 0 9 j (by omega_using [hj]) (by omega_using [hj])
  have hF9 := hc2 9 (by decide)
  have hF0 := hc2 0 (by decide)
  have hF1 := hc2 1 (by decide)
  simp only [yr] at hF9 hF0 hF1
  have hm2 : s2.gpr .r2 = VG.Proof.Poly1305.Arm.maskV := by rw [k2.gpr _ VG.Proof.Poly1305.Arm.cregs_r2, u1.gpr]; rfl
  simp only [List.cons_append, List.nil_append]
  refine VG.Proof.Poly1305.Arm.wp_mov (VG.Proof.Poly1305.Arm.op2_lsr (by decide)) fun s3 u3 => VG.Proof.Poly1305.Arm.wp_and (VG.Proof.Poly1305.Arm.op2_reg _ _) fun s4 u4 => ?_
  refine VG.Proof.Poly1305.Arm.wp_add (VG.Proof.Poly1305.Arm.op2_lsl (by decide)) fun s5 u5 => VG.Proof.Poly1305.Arm.wp_add (VG.Proof.Poly1305.Arm.op2_reg _ _) fun s6 u6 => ?_
  -- The values of `r12`, `r1` and `r3`.
  have hc9 : (s3.gpr .r12).toNat = VG.Proof.Poly1305.Arm.carryN f 0 9 9 / 2 ^ 13 := by rw [u3.gpr, VG.Proof.Poly1305.Arm.toNat_shr, hF9]
  have hc9' : VG.Proof.Poly1305.Arm.carryN f 0 9 9 / 2 ^ 13 < 2 ^ 19 := by have := (s2.gpr .r1).isLt; omega_using [hF9, hc9]
  have h12 : (s5.gpr .r12).toNat = 5 * (VG.Proof.Poly1305.Arm.carryN f 0 9 9 / 2 ^ 13) := by
    rw [u5.gpr, u4.other _ (by decide), VG.Proof.Poly1305.Arm.toNat_add_lt (by rw [VG.Proof.Poly1305.Arm.toNat_shl]; omega_using [hc9, hc9']), VG.Proof.Poly1305.Arm.toNat_shl, hc9]
    omega_using [hc9, hc9']
  have h1 : (s6.gpr .r1).toNat = VG.Proof.Poly1305.Arm.carryN f 0 9 9 % 2 ^ 13 := by
    rw [u6.other _ (by decide), u5.other _ (by decide), u4.gpr, u3.other _ (by decide),
      u3.other _ (by decide), hm2, VG.Proof.Poly1305.Arm.toNat_and_mask, hF9]
  have h3 : (s6.gpr .r3).toNat = VG.Proof.Poly1305.Arm.carryN f 0 9 0 + 5 * (VG.Proof.Poly1305.Arm.carryN f 0 9 9 / 2 ^ 13) := by
    have := hl 0 (by decide)
    rw [u6.gpr, u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide),
      VG.Proof.Poly1305.Arm.toNat_add_lt (by rw [h12, hF0]; omega_using [hF0, hc9, hc9', this]), h12, hF0]
  have h4 : (s6.gpr .r4).toNat = VG.Proof.Poly1305.Arm.carryN f 0 9 1 := by
    rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide),
      u3.other _ (by decide), hF1]
  have hm6 : s6.gpr .r2 = VG.Proof.Poly1305.Arm.maskV := by
    rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide),
      u3.other _ (by decide), hm2]
  have hk6 : VG.Proof.Poly1305.Arm.Keeps (.r2 :: .r12 :: VG.Proof.Poly1305.Arm.cregs) s s6 :=
    (u1.keeps (by simp only [List.mem_cons, reduceCtorEq, false_or, true_or])).trans ((k2.mono fun r hr => by simp only [List.mem_cons, hr, or_true]).trans ((u3.keeps (by simp only [List.mem_cons, reduceCtorEq, true_or, or_true])).trans
      ((u4.keeps (by simp only [VG.Proof.Poly1305.Arm.cregs, List.mem_cons, reduceCtorEq, true_or, or_true])).trans ((u5.keeps (by simp only [List.mem_cons, reduceCtorEq, true_or, or_true])).trans (u6.keeps (by simp only [VG.Proof.Poly1305.Arm.cregs, VG.Proof.Poly1305.Arm.yregs, List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, or_false, or_true]))))))
  refine WP.mono (VG.Proof.Poly1305.Arm.carryStep_ok (k := 0) (by decide) hm6 (by
    simp only [yr, Nat.zero_add]; rw [h3, h4]; have := hl 1 (by decide); omega_using [hF1, h3, h4, this]))
    fun s7 ⟨e1, e0, k7⟩ => ⟨fun j hj => ?_, ?_, hk6.trans (k7.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp [yr, VG.Proof.Poly1305.Arm.cregs, VG.Proof.Poly1305.Arm.yregs])⟩
  · simp only [Nat.zero_add] at e1 e0
    rcases Nat.lt_or_ge j 2 with h | h
    · obtain rfl | rfl : j = 0 ∨ j = 1 := by omega_using [hj, h]
      · rw [e0, VG.Proof.Poly1305.Arm.fold_0]; simp only [yr] at h3 ⊢; rw [h3]
      · rw [e1, VG.Proof.Poly1305.Arm.fold_1]; simp only [yr] at h3 h4 ⊢; rw [h3, h4]
    have k26 : VG.Proof.Poly1305.Arm.Keeps [.r12, .r1, .r3] s2 s6 :=
      (u3.keeps (by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, or_false])).trans ((u4.keeps (by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, or_false, or_true])).trans ((u5.keeps (by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, or_false])).trans
        (u6.keeps (by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_false, or_true]))))
    rcases Nat.lt_or_ge j 9 with h' | h'
    · have hn : ∀ j < 9, 2 ≤ j → yr j ∉ [Reg.r12, .r1, .r3] ∧ yr j ∉ [yr 0, yr (0 + 1)] := by decide +kernel
      rw [k7.gpr _ (hn j h' h).2, k26.gpr _ (hn j h' h).1, VG.Proof.Poly1305.Arm.fold_mid f h h']
      exact hc2 j hj
    · rw [show j = 9 by omega_using [hj, h, h'], k7.gpr _ (by decide), VG.Proof.Poly1305.Arm.fold_9]; exact h1
  · rw [k7.gpr _ (by simp only [yr, Nat.zero_add, List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, not_false_eq_true]), hm6]

theorem plus5_ok {K : Nat → Nat} (hK : ∀ j < 10, K j ≤ 2 ^ 13) {s : State} (hc : VG.Proof.Poly1305.Arm.Cols K s) :
    WP isa (.block plus5) s fun s' => (s'.gpr .r12).toNat = VG.Proof.Poly1305.Arm.chainT K 9 ∧ VG.Proof.Poly1305.Arm.Keeps [.r12] s s' := by
  rw [plus5]
  refine VG.Proof.Poly1305.Arm.wp_add (VG.Proof.Poly1305.Arm.op2_imm (by decide)) fun s1 u1 => ?_
  have h0 := hc 0 (by decide)
  have hK0 := hK 0 (by decide)
  simp only [yr] at h0
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun k s' => (s'.gpr .r12).toNat = VG.Proof.Poly1305.Arm.chainT K k ∧ VG.Proof.Poly1305.Arm.Keeps [.r12] s1 s')
    (fun k s' hk ⟨h12, hk'⟩ => ?_) 9 (Nat.le_refl _) s1
    ⟨by rw [u1.gpr, VG.Proof.Poly1305.Arm.toNat_add_lt (by rw [h0]; simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega_using [hK0, h0]), h0]; rfl, Keeps.refl _ _⟩)
    fun s' ⟨h, k⟩ => ⟨h, (u1.keeps (by simp only [List.mem_cons, List.not_mem_nil, or_false])).trans k⟩
  have hy : (s'.gpr (yr (k + 1))).toNat = K (k + 1) := by
    rw [hk'.gpr _ (by have := (VG.Proof.Poly1305.Arm.yr_ne' (k + 1) (by omega_using [hk])).2.2; simpa using this),
      u1.other _ (VG.Proof.Poly1305.Arm.yr_ne' (k + 1) (by omega_using [hk])).2.2]
    exact hc (k + 1) (by omega_using [hk])
  have hle := VG.Proof.Poly1305.Arm.chainT_le K hK k (by omega_using [hk])
  have hle' := hK (k + 1) (by omega_using [hk])
  refine VG.Proof.Poly1305.Arm.wp_add (VG.Proof.Poly1305.Arm.op2_lsr (by decide)) fun s2 u2 => WP.block_nil ⟨?_, hk'.trans (u2.keeps (by simp only [List.mem_cons, List.not_mem_nil, or_false]))⟩
  rw [u2.gpr, VG.Proof.Poly1305.Arm.toNat_add_lt (by rw [VG.Proof.Poly1305.Arm.toNat_shr, hy, h12]; omega_using [hy, hle, hle']), VG.Proof.Poly1305.Arm.toNat_shr, hy, h12]
  rfl

theorem addC_ok {s : State} {t k0 : Nat} (ht : (s.gpr .r12).toNat = t) (ht' : t < 2 ^ 20)
    (h3 : (s.gpr .r3).toNat = k0) (hk0 : k0 < 2 ^ 20) :
    WP isa (.block addC) s fun s' => (s'.gpr .r3).toNat = k0 + 5 * (t / 2 ^ 13) ∧
      VG.Proof.Poly1305.Arm.Keeps [.r12, .r3] s s' := by
  rw [addC]
  refine VG.Proof.Poly1305.Arm.wp_mov (VG.Proof.Poly1305.Arm.op2_lsr (by decide)) fun s1 u1 => VG.Proof.Poly1305.Arm.wp_add (VG.Proof.Poly1305.Arm.op2_lsl (by decide)) fun s2 u2 => ?_
  refine VG.Proof.Poly1305.Arm.wp_add (VG.Proof.Poly1305.Arm.op2_reg _ _) fun s3 u3 => WP.block_nil ⟨?_, (u1.keeps (by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, or_false])).trans
    ((u2.keeps (by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, or_false])).trans (u3.keeps (by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_false, or_true])))⟩
  have e1 : (s1.gpr .r12).toNat = t / 2 ^ 13 := by rw [u1.gpr, VG.Proof.Poly1305.Arm.toNat_shr, ht]
  have e2 : (s2.gpr .r12).toNat = 5 * (t / 2 ^ 13) := by
    rw [u2.gpr, VG.Proof.Poly1305.Arm.toNat_add_lt (by rw [VG.Proof.Poly1305.Arm.toNat_shl, e1]; omega_using [ht, ht']), VG.Proof.Poly1305.Arm.toNat_shl, e1]; omega_using [ht, ht']
  rw [u3.gpr, u2.other _ (by decide), u1.other _ (by decide),
    VG.Proof.Poly1305.Arm.toNat_add_lt (by rw [h3, e2]; omega_using [ht, ht', h3, hk0, e1]), h3, e2]

theorem reduceRegs_ok {E : Nat → Nat} (hE : ∀ j < 10, E j < 2 ^ 32 - 2 ^ 19) {s : State}
    (hc : VG.Proof.Poly1305.Arm.Cols E s) :
    WP isa (.block reduceRegs) s fun s' =>
      VG.Proof.Poly1305.Arm.Cols (VG.Proof.Poly1305.Arm.redL E) s' ∧ s'.gpr .r2 = VG.Proof.Poly1305.Arm.maskV ∧ VG.Proof.Poly1305.Arm.Keeps (.r2 :: .r12 :: VG.Proof.Poly1305.Arm.cregs) s s' := by
  obtain ⟨hH, hK, hK', -, -⟩ := VG.Proof.Poly1305.Arm.red_facts E hE
  rw [reduceRegs]
  simp only [List.append_assoc]
  refine WP.append (VG.Proof.Poly1305.Arm.carryFold_ok hE hc) fun s1 ⟨hc1, hm1, k1⟩ => ?_
  refine WP.append (VG.Proof.Poly1305.Arm.carries_ok 1 8 (by decide) hH hc1 hm1) fun s2 ⟨hc2, k2⟩ => ?_
  refine WP.append (VG.Proof.Poly1305.Arm.plus5_ok hK hc2) fun s3 ⟨h12, k3⟩ => ?_
  have hc3 : VG.Proof.Poly1305.Arm.Cols (VG.Proof.Poly1305.Arm.redK E) s3 := hc2.keep k3 fun j hj => by simpa using (VG.Proof.Poly1305.Arm.yr_ne' j hj).2.2
  have ht : VG.Proof.Poly1305.Arm.chainT (VG.Proof.Poly1305.Arm.redK E) 9 < 2 ^ 20 := by have := VG.Proof.Poly1305.Arm.chainT_le _ hK 9 (by decide); omega_using [this]
  have h30 : (s3.gpr .r3).toNat = VG.Proof.Poly1305.Arm.redK E 0 := hc3 0 (by decide)
  have hk0 := hK 0 (by decide)
  refine WP.append (VG.Proof.Poly1305.Arm.addC_ok h12 ht h30 (by omega_using [h30, hk0])) fun s4 ⟨h4, k4⟩ => ?_
  have hc4 : VG.Proof.Poly1305.Arm.Cols (VG.Proof.Poly1305.Arm.redK' E) s4 := fun j hj => by
    simp only [VG.Proof.Poly1305.Arm.redK']
    split
    · rename_i e; subst e; show (s4.gpr .r3).toNat = _; rw [h4, VG.Proof.Poly1305.Arm.chainT_top]; rfl
    · rw [k4.gpr _ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨(VG.Proof.Poly1305.Arm.yr_ne' j hj).2.2, fun e => by have := VG.Proof.Poly1305.Arm.yr_inj _ hj 0 (by decide) e; omega⟩)]
      exact hc3 j hj
  have hm4 : s4.gpr .r2 = VG.Proof.Poly1305.Arm.maskV := by
    rw [k4.gpr _ (by decide), k3.gpr _ (by decide), k2.gpr _ VG.Proof.Poly1305.Arm.cregs_r2, hm1]
  rw [carry3]
  refine WP.append (VG.Proof.Poly1305.Arm.carries_ok 0 9 (by decide) hK' hc4 hm4) fun s5 ⟨hc5, k5⟩ => ?_
  have hm5 : s5.gpr .r2 = VG.Proof.Poly1305.Arm.maskV := by rw [k5.gpr _ VG.Proof.Poly1305.Arm.cregs_r2, hm4]
  refine VG.Proof.Poly1305.Arm.wp_and (VG.Proof.Poly1305.Arm.op2_reg _ _) fun s6 u6 => WP.block_nil ⟨fun j hj => ?_, ?_, ?_⟩
  · simp only [VG.Proof.Poly1305.Arm.redL]
    split
    · rename_i e; subst e
      have := hc5 9 (by decide)
      simp only [yr] at this ⊢
      rw [u6.gpr, hm5, VG.Proof.Poly1305.Arm.toNat_and_mask, this]
    · rw [u6.other _ (fun e => by have := VG.Proof.Poly1305.Arm.yr_inj _ hj 9 (by decide) e; omega)]
      exact hc5 j hj
  · rw [u6.other _ (by decide), hm5]
  · refine k1.trans ((k2.mono fun r hr => by simp only [List.mem_cons, hr, or_true]).trans ((k3.mono (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq, reduceCtorEq, true_or, or_true])).trans
      ((k4.mono (by simp only [List.mem_cons, List.not_mem_nil, or_false, VG.Proof.Poly1305.Arm.cregs, VG.Proof.Poly1305.Arm.yregs, forall_eq_or_imp, reduceCtorEq, or_self, or_true, forall_eq, and_self])).trans ((k5.mono fun r hr => by simp only [List.mem_cons, hr, or_true]).trans
        (u6.keeps (by simp only [VG.Proof.Poly1305.Arm.cregs, List.mem_cons, reduceCtorEq, true_or, or_true]))))))

/-- The words of the limbs `L` (see `val_toWords`). -/
def tw0 (L : Nat → Nat) : Nat := L 0 + 2 ^ 13 * L 1 + 2 ^ 26 * (L 2 % 2 ^ 6)
def tw1 (L : Nat → Nat) : Nat := L 2 / 2 ^ 6 + 2 ^ 7 * L 3 + 2 ^ 20 * (L 4 % 2 ^ 12)
def tw2 (L : Nat → Nat) : Nat := L 4 / 2 ^ 12 + 2 * L 5 + 2 ^ 14 * L 6 + 2 ^ 27 * (L 7 % 2 ^ 5)
def tw3 (L : Nat → Nat) : Nat := L 7 / 2 ^ 5 + 2 ^ 8 * L 8 + 2 ^ 21 * (L 9 % 2 ^ 11)

theorem add_shl {x y : BitVec 32} {a : Nat} (h : x.toNat + y.toNat * 2 ^ a % 2 ^ 32 < 2 ^ 32) :
    (x + y <<< a).toNat = x.toNat + y.toNat * 2 ^ a % 2 ^ 32 := by
  rw [VG.Proof.Poly1305.Arm.toNat_add_lt (by rw [VG.Proof.Poly1305.Arm.toNat_shl]; exact h), VG.Proof.Poly1305.Arm.toNat_shl]

theorem shr' {x : BitVec 32} {n X : Nat} (hx : x.toNat = X) : (x >>> n).toNat = X / 2 ^ n := by
  rw [VG.Proof.Poly1305.Arm.toNat_shr, hx]

/-- `x + (y << a)`, where `x` has `a` bits: the bits of `y` that fit above them. -/
theorem add_shl2 {x y : BitVec 32} {a X Y : Nat} (hx : x.toNat = X) (hy : y.toNat = Y)
    (ha : a ≤ 32) (hX : X < 2 ^ a) : (x + y <<< a).toNat = X + 2 ^ a * (Y % 2 ^ (32 - a)) := by
  rw [BitVec.toNat_add, VG.Proof.Poly1305.Arm.toNat_shl, hx, hy, VG.Proof.Poly1305.Arm.shl_mod _ _ ha]
  exact Nat.mod_eq_of_lt (VG.Proof.Poly1305.Arm.fits hX (Nat.mod_lt _ (Nat.two_pow_pos _)) (by omega_using [ha]))

theorem toWords_ok {L : Nat → Nat} {s : State} (hc : VG.Proof.Poly1305.Arm.Cols L s) (hL : ∀ j < 9, L j < 2 ^ 13) :
    WP isa (.block toWords) s fun s' =>
      (s'.gpr .r3).toNat = VG.Proof.Poly1305.Arm.tw0 L ∧ (s'.gpr .r5).toNat = VG.Proof.Poly1305.Arm.tw1 L ∧ (s'.gpr .r7).toNat = VG.Proof.Poly1305.Arm.tw2 L ∧
      (s'.gpr .r10).toNat = VG.Proof.Poly1305.Arm.tw3 L ∧ (s'.gpr .r1).toNat = L 9 / 2 ^ 11 ∧
      VG.Proof.Poly1305.Arm.Keeps [.r1, .r3, .r5, .r7, .r10] s s' := by
  have c0 := hc 0 (by decide); have c1 := hc 1 (by decide); have c2 := hc 2 (by decide)
  have c3 := hc 3 (by decide); have c4 := hc 4 (by decide); have c5 := hc 5 (by decide)
  have c6 := hc 6 (by decide); have c7 := hc 7 (by decide); have c8 := hc 8 (by decide)
  have c9 := hc 9 (by decide)
  simp only [yr] at c0 c1 c2 c3 c4 c5 c6 c7 c8 c9
  have l0 := hL 0 (by decide); have l1 := hL 1 (by decide); have l2 := hL 2 (by decide)
  have l3 := hL 3 (by decide); have l4 := hL 4 (by decide); have l5 := hL 5 (by decide)
  have l6 := hL 6 (by decide); have l7 := hL 7 (by decide); have l8 := hL 8 (by decide)
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLeDiff, Nat.reducePow, and_self, toWords, runBlock_cons, runStep_some, runBlock_nil, exec,
    Op2.eval, isa, State.setReg, Option.map_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨?_, ?_, ?_, ?_, ?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [VG.Proof.Poly1305.Arm.add_shl2 (VG.Proof.Poly1305.Arm.add_shl2 c0 c1 (by decide) l0) c2 (by decide) (VG.Proof.Poly1305.Arm.fits l0 (VG.Proof.Poly1305.Arm.modlt l1) (by decide)),
      VG.Proof.Poly1305.Arm.modw l1 (by decide)]
    rfl
  · have x0 : L 2 / 2 ^ 6 < 2 ^ 7 := Nat.div_lt_of_lt_mul l2
    rw [VG.Proof.Poly1305.Arm.add_shl2 (VG.Proof.Poly1305.Arm.add_shl2 (VG.Proof.Poly1305.Arm.shr' c2) c3 (by decide) x0) c4 (by decide)
      (VG.Proof.Poly1305.Arm.fits x0 (VG.Proof.Poly1305.Arm.modlt l3) (by decide)), VG.Proof.Poly1305.Arm.modw l3 (by decide)]
    rfl
  · have x0 : L 4 / 2 ^ 12 < 2 ^ 1 := Nat.div_lt_of_lt_mul l4
    have x1 := VG.Proof.Poly1305.Arm.fits x0 (VG.Proof.Poly1305.Arm.modlt (k := 32 - 1) l5) (show 1 + 13 ≤ 14 by decide)
    rw [VG.Proof.Poly1305.Arm.add_shl2 (VG.Proof.Poly1305.Arm.add_shl2 (VG.Proof.Poly1305.Arm.add_shl2 (VG.Proof.Poly1305.Arm.shr' c4) c5 (by decide) x0) c6 (by decide) x1) c7 (by decide)
      (VG.Proof.Poly1305.Arm.fits x1 (VG.Proof.Poly1305.Arm.modlt l6) (by decide)), VG.Proof.Poly1305.Arm.modw l5 (by decide), VG.Proof.Poly1305.Arm.modw l6 (by decide)]
    rfl
  · have x0 : L 7 / 2 ^ 5 < 2 ^ 8 := Nat.div_lt_of_lt_mul l7
    rw [VG.Proof.Poly1305.Arm.add_shl2 (VG.Proof.Poly1305.Arm.add_shl2 (VG.Proof.Poly1305.Arm.shr' c7) c8 (by decide) x0) c9 (by decide)
      (VG.Proof.Poly1305.Arm.fits x0 (VG.Proof.Poly1305.Arm.modlt l8) (by decide)), VG.Proof.Poly1305.Arm.modw l8 (by decide)]
    rfl
  · rw [VG.Proof.Poly1305.Arm.toNat_shr, c9]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h3, h5, h7, h10⟩ := hr
    simp only [h1, ↓reduceIte, h10, h7, h5, h3]

end VG.Proof.Poly1305.Arm

end

-- Formerly the module `VerifiedGarbage.Proof.Poly1305.Arm.Absorb`.
section

section

/-!
# Poly1305 on 32-bit ARM: the columns of `h r`

`multiply` computes the columns `col h r` (above) into `r3`–`r12`, row by row:
row `j` loads `h j` (two limbs are packed in each word at `[0, 20)`) and adds
its products with the limbs of `r` (at `rOff i`) to the columns (`mac_step`).
-/

namespace VG.Proof.Poly1305.Arm

open VG VG.Arm VG.Impl.Poly1305.Arm

/-- Limb `i` of `r` as `loadR i` loads it from the memory `m` of the state at `B`. -/
def rval (m : Mem) (B : Addr) (i : Nat) : Nat :=
  if i = 4 ∨ i = 9 then (m (B + BitVec.ofNat 64 (rOff i))).toNat
  else (m.readW (B + BitVec.ofNat 64 (rOff i)) 32).toNat

theorem rOff_lt : ∀ i < 10, rOff i + 4 ≤ 128 := by decide +kernel

/-- The bound on the limbs of `h` that are multiplied. -/
abbrev Hb : Nat := 2 ^ 13 + 2 ^ 9

theorem col_lt {h r : Nat → Nat} (hh : ∀ j < 10, h j ≤ VG.Proof.Poly1305.Arm.Hb) (hr : ∀ i < 10, r i < 2 ^ 13) {k : Nat}
    (hk : k < 10) : VG.Proof.Poly1305.Arm.col h r k ≤ 3564723200 := by
  have := VG.Proof.Poly1305.Arm.col_le (h := h) (r := r) (R := 2 ^ 13 - 1) hh (fun i hi => by have := hr i hi; omega_using [this]) hk
  simp only [VG.Proof.Poly1305.Arm.Hb] at this
  omega_using [this]

section
variable {st : BitVec 32} (hfit : st.toNat + 128 ≤ 2 ^ 32)
include hfit

theorem macCore_ok {i : Nat} (hi : i < 10) {X : Reg} (hX2 : X ≠ .r2)
    {s : State} (h0 : s.gpr .r0 = st) (hw : VG.Proof.Poly1305.Arm.stR st ∈ s.wr)
    (hb : (s.gpr X).toNat + (s.gpr .r1).toNat * VG.Proof.Poly1305.Arm.rval s.mem (State.addr st) i < 2 ^ 32) :
    WP isa (.block [loadR i, .mul .r2 .r1 .r2, .dp .add X X (.reg .r2)]) s fun s' =>
      (s'.gpr X).toNat = (s.gpr X).toNat + (s.gpr .r1).toNat * VG.Proof.Poly1305.Arm.rval s.mem (State.addr st) i ∧
        VG.Proof.Poly1305.Arm.Keeps [.r2, X] s s' := by
  have hro := VG.Proof.Poly1305.Arm.rOff_lt i hi
  have hA : State.addr (s.gpr .r0 + BitVec.ofNat 32 (rOff i)) = State.addr st + BitVec.ofNat 64 (rOff i) := by
    rw [h0]; exact VG.Proof.Poly1305.Arm.ea hfit (by omega_using [hro])
  have finish : ∀ s1 : State, ∀ v : BitVec 32, VG.Proof.Poly1305.Arm.Upd s s1 .r2 v → v.toNat = VG.Proof.Poly1305.Arm.rval s.mem (State.addr st) i →
      WP isa (.block [.mul .r2 .r1 .r2, .dp .add X X (.reg .r2)]) s1 fun s' =>
        (s'.gpr X).toNat = (s.gpr X).toNat + (s.gpr .r1).toNat * VG.Proof.Poly1305.Arm.rval s.mem (State.addr st) i ∧
          VG.Proof.Poly1305.Arm.Keeps [.r2, X] s s' := fun s1 v u1 hv =>
    VG.Proof.Poly1305.Arm.wp_mul fun s2 u2 => VG.Proof.Poly1305.Arm.wp_add (VG.Proof.Poly1305.Arm.op2_reg _ _) fun s3 u3 => WP.block_nil ⟨by
      have e1 : s1.gpr .r1 = s.gpr .r1 := u1.other _ (by decide)
      have eX : s1.gpr X = s.gpr X := u1.other _ hX2
      have hp : (s2.gpr .r2).toNat = (s.gpr .r1).toNat * VG.Proof.Poly1305.Arm.rval s.mem (State.addr st) i := by
        rw [u2.gpr, u1.gpr, e1, VG.Proof.Poly1305.Arm.toNat_mul_lt (by rw [hv]; omega_using [hb]), hv]
      rw [u3.gpr, u2.other _ hX2, eX, VG.Proof.Poly1305.Arm.toNat_add_lt (by rw [hp]; exact hb), hp],
      (u1.keeps (by simp only [List.mem_cons, List.not_mem_nil, or_false, true_or])).trans ((u2.keeps (by simp only [List.mem_cons, List.not_mem_nil, or_false, true_or])).trans (u3.keeps (by simp only [List.mem_cons, List.not_mem_nil, or_false, or_true])))⟩
  by_cases h49 : i = 4 ∨ i = 9
  · simp only [loadR, h49, ite_true]
    refine VG.Proof.Poly1305.Arm.wp_ldrb (by omega_using [hro]) hA (VG.Proof.Poly1305.Arm.inSt hw (by omega_using [hro])) fun s1 u1 => finish s1 _ u1 ?_
    simp only [VG.Proof.Poly1305.Arm.rval, h49, ite_true]
    rfl
  · simp only [loadR, h49, ite_false]
    refine VG.Proof.Poly1305.Arm.wp_ldr (by omega_using [hro]) hA (VG.Proof.Poly1305.Arm.inSt hw (by omega_using [hro])) fun s1 u1 => finish s1 _ u1 ?_
    simp only [VG.Proof.Poly1305.Arm.rval, h49, ite_false]

/-- In row `j`, after the products of `r i` for `i < n`, relative to the state
`s₀` in which the multiplication starts. -/
structure MI (h r : Nat → Nat) (s₀ : State) (j n : Nat) (s : State) : Prop where
  cols : ∀ k < 10, (s.gpr (xr k)).toNat = VG.Proof.Poly1305.Arm.psum h r j n k
  a : (s.gpr .r1).toNat = if 0 < j ∧ 10 - j < n then 5 * h j else h j
  keeps : VG.Proof.Poly1305.Arm.Keeps VG.Proof.Poly1305.Arm.work s₀ s

theorem mac_step {h r : Nat → Nat} (hh : ∀ j < 10, h j ≤ VG.Proof.Poly1305.Arm.Hb) (hr : ∀ i < 10, r i < 2 ^ 13) {s₀ : State}
    (h0 : s₀.gpr .r0 = st) (hw : VG.Proof.Poly1305.Arm.stR st ∈ s₀.wr) (hR : ∀ i < 10, VG.Proof.Poly1305.Arm.rval s₀.mem (State.addr st) i = r i)
    {j : Nat} (hj : j < 10) (n : Nat) (s : State) (hn : n < 10) (hs : VG.Proof.Poly1305.Arm.MI h r s₀ j n s) :
    WP isa (.block (mac j n)) s (VG.Proof.Poly1305.Arm.MI h r s₀ j (n + 1)) := by
  have hs0 : s.gpr .r0 = st := by rw [hs.keeps.gpr _ (by decide), h0]
  have hsw : VG.Proof.Poly1305.Arm.stR st ∈ s.wr := by rw [hs.keeps.wr]; exact hw
  have hRs : VG.Proof.Poly1305.Arm.rval s.mem (State.addr st) n = r n := by rw [hs.keeps.mem]; exact hR n hn
  set k₀ := (n + j) % 10 with hk₀
  have hk₀10 : k₀ < 10 := Nat.mod_lt _ (by decide)
  have hX := VG.Proof.Poly1305.Arm.xr_ne k₀ hk₀10
  -- The core, from a state with `r1 = a` and the columns and memory of `s`.
  have core : ∀ s1 : State, VG.Proof.Poly1305.Arm.Keeps [.r1] s s1 →
      (s1.gpr .r1).toNat = (if n + j < 10 then h j else 5 * h j) →
      (s1.gpr .r1).toNat = (if 0 < j ∧ 10 - j < n + 1 then 5 * h j else h j) →
      WP isa (.block [loadR n, .mul .r2 .r1 .r2, .dp .add (xr k₀) (xr k₀) (.reg .r2)]) s1
        (VG.Proof.Poly1305.Arm.MI h r s₀ j (n + 1)) := by
    intro s1 k1 ha ha'
    have hc1 : ∀ k < 10, (s1.gpr (xr k)).toNat = VG.Proof.Poly1305.Arm.psum h r j n k := fun k hk => by
      rw [k1.gpr _ (by simpa using (VG.Proof.Poly1305.Arm.xr_ne k hk).2.1)]; exact hs.cols k hk
    have e := VG.Proof.Poly1305.Arm.psum_step h r hj hn hk₀10
    rw [VG.Proof.Poly1305.Arm.iteT hk₀] at e
    have hle := VG.Proof.Poly1305.Arm.psum_le_col h r (j := j) (n := n + 1) (k := k₀) hj
    have hcol := VG.Proof.Poly1305.Arm.col_lt hh hr hk₀10
    refine WP.mono (VG.Proof.Poly1305.Arm.macCore_ok hfit hn hX.2.2 (by rw [k1.gpr _ (by decide), hs0])
      (by rw [k1.wr]; exact hsw) ?_) fun s2 ⟨e2, k2⟩ => ⟨fun k hk => ?_, ?_, ?_⟩
    · rw [k1.mem, hRs, hc1 _ hk₀10, ha, ← e]; omega_using [e, hle, hcol]
    · by_cases ek : k = k₀
      · subst ek; rw [e2, k1.mem, hRs, hc1 _ hk₀10, ha, e]
      · rw [k2.gpr _ (by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨(VG.Proof.Poly1305.Arm.xr_ne k hk).2.2, fun h' => ek (VG.Proof.Poly1305.Arm.xr_inj _ hk _ hk₀10 h')⟩), hc1 k hk]
        have e' := VG.Proof.Poly1305.Arm.psum_step h r hj hn hk (k := k)
        rw [VG.Proof.Poly1305.Arm.iteF (by rw [← hk₀]; exact ek)] at e'
        exact e'.symm
    · rw [k2.gpr _ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨by decide, hX.2.1.symm⟩)]; exact ha'
    · exact hs.keeps.trans ((k1.mono (by simp only [List.mem_cons, List.not_mem_nil, or_false, VG.Proof.Poly1305.Arm.work, forall_eq, reduceCtorEq, or_self])).trans (k2.mono fun q hq => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · decide
        · exact VG.Proof.Poly1305.Arm.xr_work _ hk₀10))
  have hj' : h j ≤ 2 ^ 13 + 2 ^ 9 := hh j hj
  by_cases h5 : 0 < j ∧ n + j = 10
  · simp only [mac]
    rw [VG.Proof.Poly1305.Arm.iteT h5, List.cons_append, List.nil_append]
    refine VG.Proof.Poly1305.Arm.wp_add (VG.Proof.Poly1305.Arm.op2_lsl (by decide)) fun s1 u1 => core s1 (u1.keeps (by simp only [List.mem_cons, List.not_mem_nil, or_false])) ?_ ?_
    · have ha := hs.a
      rw [VG.Proof.Poly1305.Arm.iteF (by omega_using [hj, h5])] at ha
      rw [u1.gpr, VG.Proof.Poly1305.Arm.toNat_add_lt (by rw [VG.Proof.Poly1305.Arm.toNat_shl, ha]; omega_using [hj', ha]), VG.Proof.Poly1305.Arm.toNat_shl, ha, VG.Proof.Poly1305.Arm.iteF (by omega_using [h5])]
      omega_using [hj', ha]
    · have ha := hs.a
      rw [VG.Proof.Poly1305.Arm.iteF (by omega_using [hj, h5])] at ha
      rw [u1.gpr, VG.Proof.Poly1305.Arm.toNat_add_lt (by rw [VG.Proof.Poly1305.Arm.toNat_shl, ha]; omega_using [hj', ha]), VG.Proof.Poly1305.Arm.toNat_shl, ha, VG.Proof.Poly1305.Arm.iteT (by omega_using [hj, h5])]
      omega_using [hj', ha]
  · simp only [mac, h5, ite_false, List.nil_append]
    refine core s (Keeps.refl _ _) ?_ ?_
    · rw [hs.a]; split <;> split <;> omega
    · rw [hs.a]; split <;> split <;> omega

/-- `h`, two limbs per word, at `[0, 20)` of the state at `B`. -/
def HMem (h : Nat → Nat) (m : Mem) (B : Addr) : Prop :=
  ∀ i < 5, (m.readW (B + BitVec.ofNat 64 (4 * i)) 32).toNat = h (2 * i) + 2 ^ 16 * h (2 * i + 1)

theorem loadH_ok {h : Nat → Nat} (hh : ∀ j < 10, h j ≤ VG.Proof.Poly1305.Arm.Hb) {j : Nat} (hj : j < 10) {s : State}
    (h0 : s.gpr .r0 = st) (hw : VG.Proof.Poly1305.Arm.stR st ∈ s.wr) (hH : VG.Proof.Poly1305.Arm.HMem h s.mem (State.addr st)) :
    WP isa (.block (loadH j)) s fun s' => (s'.gpr .r1).toNat = h j ∧ VG.Proof.Poly1305.Arm.Keeps [.r1] s s' := by
  have hb : ∀ j < 10, h j < 2 ^ 16 := fun j hj => by have := hh j hj; simp only [VG.Proof.Poly1305.Arm.Hb] at this; omega_using [this]
  obtain ⟨i, rfl | rfl⟩ : ∃ i, j = 2 * i ∨ j = 2 * i + 1 := ⟨j / 2, by omega_using []⟩
  · have hw' := hH i (by omega_using [hj])
    simp only [loadH, show 2 * i % 2 = 0 by omega_using [], ite_true]
    refine VG.Proof.Poly1305.Arm.wp_ldr (by omega_using [hj]) (by rw [h0, show 2 * (2 * i) = 4 * i by omega_using []]; exact VG.Proof.Poly1305.Arm.ea hfit (by omega_using [hj]))
      (VG.Proof.Poly1305.Arm.inSt hw (by omega_using [hj])) fun s1 u1 => VG.Proof.Poly1305.Arm.wp_mov (VG.Proof.Poly1305.Arm.op2_lsl (by decide)) fun s2 u2 =>
        VG.Proof.Poly1305.Arm.wp_mov (VG.Proof.Poly1305.Arm.op2_lsr (by decide)) fun s3 u3 => WP.block_nil ⟨?_, (u1.keeps (by simp only [List.mem_cons, List.not_mem_nil, or_false])).trans
          ((u2.keeps (by simp only [List.mem_cons, List.not_mem_nil, or_false])).trans (u3.keeps (by simp only [List.mem_cons, List.not_mem_nil, or_false])))⟩
    rw [u3.gpr, u2.gpr, u1.gpr, VG.Proof.Poly1305.Arm.toNat_shr, VG.Proof.Poly1305.Arm.toNat_shl, hw']
    have := hb (2 * i) (by omega_using [hj]); have := hb (2 * i + 1) (by omega_using [hj])
    omega
  · have hw' := hH i (by omega_using [hj])
    simp only [loadH, show (2 * i + 1) % 2 = 1 by omega_using [], show 1 ≠ 0 by decide, ite_false,
      show 2 * i + 1 - 1 = 2 * i by omega_using [hj]]
    refine VG.Proof.Poly1305.Arm.wp_ldr (by omega_using [hj]) (by rw [h0, show 2 * (2 * i) = 4 * i by omega_using []]; exact VG.Proof.Poly1305.Arm.ea hfit (by omega_using [hj]))
      (VG.Proof.Poly1305.Arm.inSt hw (by omega_using [hj])) fun s1 u1 => VG.Proof.Poly1305.Arm.wp_mov (VG.Proof.Poly1305.Arm.op2_lsr (by decide)) fun s2 u2 =>
        WP.block_nil ⟨?_, (u1.keeps (by simp only [List.mem_cons, List.not_mem_nil, or_false])).trans (u2.keeps (by simp only [List.mem_cons, List.not_mem_nil, or_false]))⟩
    rw [u2.gpr, u1.gpr, VG.Proof.Poly1305.Arm.toNat_shr, hw']
    have := hb (2 * i) (by omega_using [hj])
    omega_using [this]

theorem row_ok {h r : Nat → Nat} (hh : ∀ j < 10, h j ≤ VG.Proof.Poly1305.Arm.Hb) (hr : ∀ i < 10, r i < 2 ^ 13) {s₀ : State}
    (h0 : s₀.gpr .r0 = st) (hw : VG.Proof.Poly1305.Arm.stR st ∈ s₀.wr) (hR : ∀ i < 10, VG.Proof.Poly1305.Arm.rval s₀.mem (State.addr st) i = r i)
    (hH : VG.Proof.Poly1305.Arm.HMem h s₀.mem (State.addr st)) (j : Nat) (s : State) (hj : j < 10)
    (hs : (∀ k < 10, (s.gpr (xr k)).toNat = VG.Proof.Poly1305.Arm.psum h r j 0 k) ∧ VG.Proof.Poly1305.Arm.Keeps VG.Proof.Poly1305.Arm.work s₀ s) :
    WP isa (.block (row j)) s fun s' =>
      (∀ k < 10, (s'.gpr (xr k)).toNat = VG.Proof.Poly1305.Arm.psum h r (j + 1) 0 k) ∧ VG.Proof.Poly1305.Arm.Keeps VG.Proof.Poly1305.Arm.work s₀ s' := by
  obtain ⟨hc, hk⟩ := hs
  rw [row]
  refine WP.append (VG.Proof.Poly1305.Arm.loadH_ok hfit hh hj (by rw [hk.gpr _ (by decide), h0]) (by rw [hk.wr]; exact hw)
    (by rw [hk.mem]; exact hH)) fun s1 ⟨ha, k1⟩ => ?_
  refine WP.mono (wp_range_flatMap (M := isa) (VG.Proof.Poly1305.Arm.MI h r s₀ j) (fun n s' hn hs' =>
    VG.Proof.Poly1305.Arm.mac_step hfit hh hr h0 hw hR hj n s' hn hs') 10 (Nat.le_refl _) s1 ⟨fun k hk' => ?_, ?_, ?_⟩)
    fun s' hs' => ⟨fun k hk' => by rw [hs'.cols k hk', VG.Proof.Poly1305.Arm.psum_row], hs'.keeps⟩
  · rw [k1.gpr _ (by simpa using (VG.Proof.Poly1305.Arm.xr_ne k hk').2.1)]; exact hc k hk'
  · rw [ha, VG.Proof.Poly1305.Arm.iteF (by omega_using [])]
  · exact hk.trans (k1.mono (by simp only [List.mem_cons, List.not_mem_nil, or_false, VG.Proof.Poly1305.Arm.work, forall_eq, reduceCtorEq, or_self]))

omit hfit in
theorem zeroX_ok {s : State} :
    WP isa (.block zeroX) s fun s' => (∀ k < 10, (s'.gpr (xr k)).toNat = 0) ∧ VG.Proof.Poly1305.Arm.Keeps VG.Proof.Poly1305.Arm.work s s' := by
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun n s' => (∀ k < n, (s'.gpr (xr k)).toNat = 0) ∧ VG.Proof.Poly1305.Arm.Keeps VG.Proof.Poly1305.Arm.work s s')
    (fun n s' hn ⟨hz, hk⟩ => VG.Proof.Poly1305.Arm.wp_mov (VG.Proof.Poly1305.Arm.op2_imm (by decide)) fun s1 u1 => WP.block_nil ⟨fun k hk' => ?_,
      hk.trans (u1.keeps (VG.Proof.Poly1305.Arm.xr_work n hn))⟩) 10 (Nat.le_refl _) s ⟨fun _ h => absurd h (by omega_using [h]), Keeps.refl _ _⟩)
    fun s' h => h
  rcases Nat.lt_succ_iff_lt_or_eq.mp hk' with h' | rfl
  · rw [u1.other _ (fun e => absurd (VG.Proof.Poly1305.Arm.xr_inj _ (by omega_using [hn, h']) _ hn e) (by omega_using [h']))]; exact hz k h'
  · rw [u1.gpr]; rfl

theorem multiply_ok {h r : Nat → Nat} (hh : ∀ j < 10, h j ≤ VG.Proof.Poly1305.Arm.Hb) (hr : ∀ i < 10, r i < 2 ^ 13) {s₀ : State}
    (h0 : s₀.gpr .r0 = st) (hw : VG.Proof.Poly1305.Arm.stR st ∈ s₀.wr) (hR : ∀ i < 10, VG.Proof.Poly1305.Arm.rval s₀.mem (State.addr st) i = r i)
    (hH : VG.Proof.Poly1305.Arm.HMem h s₀.mem (State.addr st)) :
    WP isa (.block multiply) s₀ fun s' =>
      (∀ k < 10, (s'.gpr (xr k)).toNat = VG.Proof.Poly1305.Arm.col h r k) ∧ VG.Proof.Poly1305.Arm.Keeps VG.Proof.Poly1305.Arm.work s₀ s' := by
  rw [multiply]
  refine WP.append VG.Proof.Poly1305.Arm.zeroX_ok fun s1 ⟨hz, k1⟩ => ?_
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun j s => (∀ k < 10, (s.gpr (xr k)).toNat = VG.Proof.Poly1305.Arm.psum h r j 0 k) ∧ VG.Proof.Poly1305.Arm.Keeps VG.Proof.Poly1305.Arm.work s₀ s)
    (fun j s hj hs => VG.Proof.Poly1305.Arm.row_ok hfit hh hr h0 hw hR hH j s hj hs) 10 (Nat.le_refl _) s1
    ⟨fun k hk => by rw [hz k hk, VG.Proof.Poly1305.Arm.psum_zero], k1⟩)
    fun s' ⟨hc, hk⟩ => ⟨fun k hk' => by rw [hc k hk', VG.Proof.Poly1305.Arm.psum_ten], hk⟩

end

end VG.Proof.Poly1305.Arm

end

/-!
# Poly1305 on 32-bit ARM: absorbing a block

`absorb pad` adds the 16 bytes at `r1` (and `2¹²⁸` if `pad`) to the columns
`D` (`D 0`–`D 8` in `r3`–`r11`, `D 9` at `[16, 20)` of the state: `ColsD`),
carries them into `h`, packs `h` into `[0, 20)` and multiplies it by `r`
(`absorb_ok`).
-/

namespace VG.Proof.Poly1305.Arm

open VG VG.Arm VG.Impl.Poly1305.Arm
open VG.Spec.Poly1305 (P)

/-- The columns `D`: `D 0`–`D 8` in `r3`–`r11`, `D 9` at `[16, 20)` of the state at `B`. -/
def ColsD (D : Nat → Nat) (B : Addr) (s : State) : Prop :=
  (∀ k < 9, (s.gpr (yr k)).toNat = D k) ∧ (s.mem.readW (B + BitVec.ofNat 64 16) 32).toNat = D 9

/-- The 128-bit number at `r1`, as `addWords` reads it. -/
def msgVal (s : State) : Nat :=
  (VG.Proof.Poly1305.Arm.word s 0).toNat + 2 ^ 32 * (VG.Proof.Poly1305.Arm.word s 1).toNat + 2 ^ 64 * (VG.Proof.Poly1305.Arm.word s 2).toNat + 2 ^ 96 * (VG.Proof.Poly1305.Arm.word s 3).toNat

/-- `s'` is `s` but for the registers `ws`, the flags and the memory in `F`. -/
structure KeepsF (ws : List Reg) (F : List Region) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ ws → s'.gpr r = s.gpr r
  frame : Frame F s.mem s'.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Keeps.keepsF {ws : List Reg} {s s' : State} (h : VG.Proof.Poly1305.Arm.Keeps ws s s') (F : List Region) :
    VG.Proof.Poly1305.Arm.KeepsF ws F s s' := ⟨h.gpr, h.mem ▸ Frame.refl _ _, h.rd, h.wr, h.sp⟩

theorem KeepsF.trans {ws : List Reg} {F : List Region} {s₁ s₂ s₃ : State} (h₁ : VG.Proof.Poly1305.Arm.KeepsF ws F s₁ s₂)
    (h₂ : VG.Proof.Poly1305.Arm.KeepsF ws F s₂ s₃) : VG.Proof.Poly1305.Arm.KeepsF ws F s₁ s₃ :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₁.frame.trans h₂.frame, h₂.rd.trans h₁.rd,
    h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp⟩

theorem KeepsF.mono {ws ws' : List Reg} {F : List Region} {s s' : State} (h : VG.Proof.Poly1305.Arm.KeepsF ws F s s')
    (hs : ∀ r ∈ ws, r ∈ ws') : VG.Proof.Poly1305.Arm.KeepsF ws' F s s' :=
  ⟨fun r hr => h.gpr r fun h' => hr (hs r h'), h.frame, h.rd, h.wr, h.sp⟩

/-- `[0, 20)` of the state. -/
abbrev accR (B : Addr) : Region := ⟨B, 20⟩

section
variable {st : BitVec 32} (hfit : st.toNat + 128 ≤ 2 ^ 32)
include hfit

/-- After packing `i` words of `H`. -/
structure PI (H : Nat → Nat) (st : BitVec 32) (s₀ : State) (i : Nat) (s : State) : Prop where
  mem : ∀ i' < i, (s.mem.readW (State.addr st + BitVec.ofNat 64 (4 * i')) 32).toNat =
    H (2 * i') + 2 ^ 16 * H (2 * i' + 1)
  cols : ∀ k < 10, 2 * i ≤ k → (s.gpr (yr k)).toNat = H k
  keeps : VG.Proof.Poly1305.Arm.KeepsF VG.Proof.Poly1305.Arm.work [VG.Proof.Poly1305.Arm.accR (State.addr st)] s₀ s

theorem pack_step {H : Nat → Nat} (hH : ∀ k < 10, H k < 2 ^ 16) {s₀ : State} (h0 : s₀.gpr .r0 = st)
    (hw : VG.Proof.Poly1305.Arm.stR st ∈ s₀.wr) (i : Nat) (s : State) (hi : i < 5) (hs : VG.Proof.Poly1305.Arm.PI H st s₀ i s) :
    WP isa (.block [.dp .add (yr (2 * i)) (yr (2 * i)) (.shifted (yr (2 * i + 1)) .lsl 16),
      .str (yr (2 * i)) .r0 (4 * i)]) s (VG.Proof.Poly1305.Arm.PI H st s₀ (i + 1)) := by
  have hs0 : s.gpr .r0 = st := by rw [hs.keeps.gpr _ (by decide), h0]
  have hsw : VG.Proof.Poly1305.Arm.stR st ∈ s.wr := by rw [hs.keeps.wr]; exact hw
  have hne : yr (2 * i) ≠ yr (2 * i + 1) := fun e => absurd (VG.Proof.Poly1305.Arm.yr_inj _ (by omega_using [hi]) _ (by omega_using [hi]) e) (by omega_using [])
  refine VG.Proof.Poly1305.Arm.wp_add (VG.Proof.Poly1305.Arm.op2_lsl (by decide)) fun s1 u1 => ?_
  have hv : (s1.gpr (yr (2 * i))).toNat = H (2 * i) + 2 ^ 16 * H (2 * i + 1) := by
    have a := hs.cols (2 * i) (by omega_using [hi]) (Nat.le_refl _)
    have b := hs.cols (2 * i + 1) (by omega_using [hi]) (by omega_using [])
    have := hH (2 * i) (by omega_using [hi]); have := hH (2 * i + 1) (by omega_using [hi])
    rw [u1.gpr, VG.Proof.Poly1305.Arm.toNat_add_lt (by rw [VG.Proof.Poly1305.Arm.toNat_shl, a, b]; omega), VG.Proof.Poly1305.Arm.toNat_shl, a, b]
    omega_using [b, this]
  refine VG.Proof.Poly1305.Arm.wp_str (off := 4 * i) (a := State.addr st + BitVec.ofNat 64 (4 * i)) (by omega_using [hi]) (by rw [u1.other _ (VG.Proof.Poly1305.Arm.yr_ne' (2 * i) (by omega_using [hi])).1.symm, hs0]; exact VG.Proof.Poly1305.Arm.ea hfit (off := 4 * i) (by omega_using [hi]))
    (by rw [u1.wr]; exact VG.Proof.Poly1305.Arm.outSt hsw (off := 4 * i) (n := 4) (by omega_using [hi])) fun s2 u2 => WP.block_nil ⟨fun i' hi' => ?_, ?_, ?_⟩
  · rw [u2.mem]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with h' | rfl
    · rw [VG.Proof.Poly1305.Arm.readW_writeW_off _ _ _ (by omega_using [hi, h']) (by omega_using [hi]) (by omega_using [h']), u1.mem]; exact hs.mem i' h'
    · rw [Mem.readW_writeW_self32]; exact hv
  · intro k hk hk'
    rw [u2.gpr, u1.other _ (fun e => absurd (VG.Proof.Poly1305.Arm.yr_inj _ hk _ (by omega_using [hi]) e) (by omega_using [hk']))]
    exact hs.cols k hk (by omega_using [hk'])
  · refine hs.keeps.trans ⟨fun r hr => ?_, ?_, u2.rd.trans u1.rd, u2.wr.trans u1.wr, u2.sp.trans u1.sp⟩
    · rw [u2.gpr, u1.other _ (fun e => hr (by rw [e]; exact VG.Proof.Poly1305.Arm.yr_work _ (by omega_using [hi])))]
    · rw [u2.mem, u1.mem]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (VG.Proof.Poly1305.Arm.contains_off (by omega_using [hi]) (by omega_using [hi]))

theorem pack_ok {H : Nat → Nat} (hH : ∀ k < 10, H k < 2 ^ 16) {s : State} (h0 : s.gpr .r0 = st)
    (hw : VG.Proof.Poly1305.Arm.stR st ∈ s.wr) (hc : VG.Proof.Poly1305.Arm.Cols H s) :
    WP isa (.block pack) s fun s' => VG.Proof.Poly1305.Arm.HMem H s'.mem (State.addr st) ∧
      VG.Proof.Poly1305.Arm.KeepsF VG.Proof.Poly1305.Arm.work [VG.Proof.Poly1305.Arm.accR (State.addr st)] s s' := by
  refine WP.mono (wp_range_flatMap (M := isa) (VG.Proof.Poly1305.Arm.PI H st s) (fun i s' hi hs => VG.Proof.Poly1305.Arm.pack_step hfit hH h0 hw i s'
    hi hs) 5 (Nat.le_refl _) s ⟨fun _ h => absurd h (by omega_using [h]), fun k hk _ => hc k hk,
      (Keeps.refl _ _).keepsF _⟩) fun s' h => ⟨h.mem, h.keeps⟩

end

theorem accR_disjoint (B : Addr) {a n : Nat} (ha : 20 ≤ a) (hn : a + n ≤ 128) :
    (⟨B + BitVec.ofNat 64 a, n⟩ : Region).Disjoint (VG.Proof.Poly1305.Arm.accR B) :=
  Offset.disjoint_base B (by omega_using [ha]) (by omega_using [hn])

theorem rval_frame {m m' : Mem} {B : Addr} (hf : Frame [VG.Proof.Poly1305.Arm.accR B] m m') {i : Nat} (hi : i < 10) :
    VG.Proof.Poly1305.Arm.rval m' B i = VG.Proof.Poly1305.Arm.rval m B i := by
  have hro := VG.Proof.Poly1305.Arm.rOff_lt i hi
  have h88 : 88 ≤ rOff i := by have : ∀ i < 10, 88 ≤ rOff i := by decide +kernel
                               exact this i hi
  simp only [VG.Proof.Poly1305.Arm.rval]
  split
  · congr 1
    refine hf _ fun r hr hc => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact VG.Proof.Poly1305.Arm.accR_disjoint B (a := rOff i) (n := 1) (by omega_using [hro, h88]) (by omega_using [hro, h88]) _
      (Region.contains_self _ _ |>.byte (by simp only [BitVec.sub_self, BitVec.toNat_ofNat, Nat.reducePow, Nat.zero_mod, Nat.lt_add_one])) hc
  · rw [hf.readW (r := ⟨B + BitVec.ofNat 64 (rOff i), 4⟩) (Region.contains_self _ _) (by
      simp only [List.mem_singleton, forall_eq]; exact VG.Proof.Poly1305.Arm.accR_disjoint B (by omega_using [hro, h88]) (by omega_using [hro])) (by decide)]

section
variable {st : BitVec 32} (hfit : st.toNat + 128 ≤ 2 ^ 32)
include hfit

/-- The columns after adding a block: `D` plus the limbs of the block and, if `pad`, `2¹²⁸`. -/
def addE (D : Nat → Nat) (w : Nat → Nat) (pad : Bool) : Nat → Nat :=
  fun k => D k + VG.Proof.Poly1305.Arm.mlimb (w 0) (w 1) (w 2) (w 3) k + if k = 9 ∧ pad = true then 2 ^ 11 else 0

omit hfit in
theorem val_add (f g : Nat → Nat) : VG.Proof.Poly1305.Arm.val (fun k => f k + g k) = VG.Proof.Poly1305.Arm.val f + VG.Proof.Poly1305.Arm.val g := by
  simp only [VG.Proof.Poly1305.Arm.val]; omega

omit hfit in
theorem val_addE (D w : Nat → Nat) (pad : Bool) :
    VG.Proof.Poly1305.Arm.val (VG.Proof.Poly1305.Arm.addE D w pad) = VG.Proof.Poly1305.Arm.val D + VG.Proof.Poly1305.Arm.val (VG.Proof.Poly1305.Arm.mlimb (w 0) (w 1) (w 2) (w 3)) + if pad then 2 ^ 128 else 0 := by
  unfold VG.Proof.Poly1305.Arm.addE
  rw [VG.Proof.Poly1305.Arm.val_add (fun k => D k + VG.Proof.Poly1305.Arm.mlimb (w 0) (w 1) (w 2) (w 3) k)
    (fun k => if k = 9 ∧ pad = true then 2 ^ 11 else 0), VG.Proof.Poly1305.Arm.val_add]
  cases pad <;> rfl

theorem absorb_ok (pad : Bool) {R D : Nat → Nat} (hR : ∀ i < 10, R i < 2 ^ 13)
    (hD : ∀ k < 10, D k ≤ 3564723200) {s : State} (h0 : s.gpr .r0 = st) (hw : VG.Proof.Poly1305.Arm.stR st ∈ s.wr)
    (hRm : ∀ i < 10, VG.Proof.Poly1305.Arm.rval s.mem (State.addr st) i = R i) (hc : VG.Proof.Poly1305.Arm.ColsD D (State.addr st) s)
    (hin : ∀ i < 4, InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r1 + BitVec.ofNat 32 (4 * i))) 4) :
    WP isa (.block (absorb pad)) s fun s' => ∃ D', VG.Proof.Poly1305.Arm.ColsD D' (State.addr st) s' ∧ (∀ k < 10, D' k ≤ 3564723200) ∧
      VG.Proof.Poly1305.Arm.val D' % P = (VG.Proof.Poly1305.Arm.val D + VG.Proof.Poly1305.Arm.msgVal s + if pad then 2 ^ 128 else 0) * VG.Proof.Poly1305.Arm.val R % P ∧
      VG.Proof.Poly1305.Arm.KeepsF VG.Proof.Poly1305.Arm.work [VG.Proof.Poly1305.Arm.accR (State.addr st)] s s' := by
  have hw4 : ∀ i, (VG.Proof.Poly1305.Arm.word s i).toNat < 2 ^ 32 := fun i => (VG.Proof.Poly1305.Arm.word s i).isLt
  have hEb : ∀ k < 10, VG.Proof.Poly1305.Arm.addE D (fun i => (VG.Proof.Poly1305.Arm.word s i).toNat) pad k < 2 ^ 32 - 2 ^ 19 := fun k hk => by
    have := hD k hk; have := VG.Proof.Poly1305.Arm.mlimb_lt (hw4 0) (hw4 1) (hw4 2) (hw4 3) k
    simp only [VG.Proof.Poly1305.Arm.addE]; split <;> omega
  rw [absorb]
  simp only [List.append_assoc]
  refine WP.append (VG.Proof.Poly1305.Arm.addWords_ok hin) fun s1 ⟨hc1, hr2, k1⟩ => ?_
  have e1 : ∀ k < 9, (s1.gpr (yr k)).toNat = VG.Proof.Poly1305.Arm.addE D (fun i => (VG.Proof.Poly1305.Arm.word s i).toNat) pad k := fun k hk => by
    have := hD k (by omega_using [hk]); have := VG.Proof.Poly1305.Arm.mlimb_lt (hw4 0) (hw4 1) (hw4 2) (hw4 3) k
    rw [hc1 k hk, VG.Proof.Poly1305.Arm.toNat_add_lt (by rw [VG.Proof.Poly1305.Arm.wsum_toNat _ hk, hc.1 k hk]; omega), VG.Proof.Poly1305.Arm.wsum_toNat _ hk, hc.1 k hk]
    simp only [VG.Proof.Poly1305.Arm.addE, VG.Proof.Poly1305.Arm.iteF (show ¬(k = 9 ∧ pad = true) by omega_using [hk]), Nat.add_zero]
  have hs10 : s1.gpr .r0 = st := by rw [k1.gpr _ (by decide), h0]
  have hsw1 : VG.Proof.Poly1305.Arm.stR st ∈ s1.wr := by rw [k1.wr]; exact hw
  -- `addTop pad`: column 9 into `r1`.
  have top : WP isa (.block (addTop pad ++ (carryFold ++ (pack ++ (multiply ++ [.str .r12 .r0 d9Off]))))) s1
      (fun s' => ∃ D', VG.Proof.Poly1305.Arm.ColsD D' (State.addr st) s' ∧ (∀ k < 10, D' k ≤ 3564723200) ∧
        VG.Proof.Poly1305.Arm.val D' % P = (VG.Proof.Poly1305.Arm.val D + VG.Proof.Poly1305.Arm.msgVal s + if pad then 2 ^ 128 else 0) * VG.Proof.Poly1305.Arm.val R % P ∧
        VG.Proof.Poly1305.Arm.KeepsF VG.Proof.Poly1305.Arm.work [VG.Proof.Poly1305.Arm.accR (State.addr st)] s s') := by
    -- After `addTop`: the columns `E` in registers, the memory of `s`.
    have rest : ∀ s2 : State, VG.Proof.Poly1305.Arm.Cols (VG.Proof.Poly1305.Arm.addE D (fun i => (VG.Proof.Poly1305.Arm.word s i).toNat) pad) s2 →
        VG.Proof.Poly1305.Arm.KeepsF VG.Proof.Poly1305.Arm.work [VG.Proof.Poly1305.Arm.accR (State.addr st)] s s2 → s2.mem = s.mem →
        WP isa (.block (carryFold ++ (pack ++ (multiply ++ [.str .r12 .r0 d9Off])))) s2
          (fun s' => ∃ D', VG.Proof.Poly1305.Arm.ColsD D' (State.addr st) s' ∧ (∀ k < 10, D' k ≤ 3564723200) ∧
            VG.Proof.Poly1305.Arm.val D' % P = (VG.Proof.Poly1305.Arm.val D + VG.Proof.Poly1305.Arm.msgVal s + if pad then 2 ^ 128 else 0) * VG.Proof.Poly1305.Arm.val R % P ∧
            VG.Proof.Poly1305.Arm.KeepsF VG.Proof.Poly1305.Arm.work [VG.Proof.Poly1305.Arm.accR (State.addr st)] s s') := by
      intro s2 hc2 k2 hm2
      have hs20 : s2.gpr .r0 = st := by rw [k2.gpr _ (by decide), h0]
      obtain ⟨hv, -, hf0, hf1, hfj⟩ := VG.Proof.Poly1305.Arm.fold_facts _ hEb
      have hH : ∀ k < 10, VG.Proof.Poly1305.Arm.fold (VG.Proof.Poly1305.Arm.addE D (fun i => (VG.Proof.Poly1305.Arm.word s i).toNat) pad) k ≤ VG.Proof.Poly1305.Arm.Hb := fun k hk => by
        simp only [VG.Proof.Poly1305.Arm.Hb]
        rcases Nat.lt_or_ge k 2 with h | h
        · rcases (by omega_using [hk, h] : k = 0 ∨ k = 1) with rfl | rfl <;> omega_using [hf0, hf1]
        · have := hfj k h hk; omega_using [this]
      have hH16 : ∀ k < 10, VG.Proof.Poly1305.Arm.fold (VG.Proof.Poly1305.Arm.addE D (fun i => (VG.Proof.Poly1305.Arm.word s i).toNat) pad) k < 2 ^ 16 := fun k hk => by
        have := hH k hk; simp only [VG.Proof.Poly1305.Arm.Hb] at this; omega_using [this]
      refine WP.append (VG.Proof.Poly1305.Arm.carryFold_ok hEb hc2) fun s3 ⟨hc3, _, k3⟩ => ?_
      have hs30 : s3.gpr .r0 = st := by rw [k3.gpr _ (by decide), hs20]
      have hw3 : VG.Proof.Poly1305.Arm.stR st ∈ s3.wr := by rw [k3.wr, k2.wr]; exact hw
      refine WP.append (VG.Proof.Poly1305.Arm.pack_ok hfit hH16 hs30 hw3 hc3) fun s4 ⟨hHm, k4⟩ => ?_
      have hs40 : s4.gpr .r0 = st := by rw [k4.gpr _ (by decide), hs30]
      have hw4' : VG.Proof.Poly1305.Arm.stR st ∈ s4.wr := by rw [k4.wr]; exact hw3
      have hR4 : ∀ i < 10, VG.Proof.Poly1305.Arm.rval s4.mem (State.addr st) i = R i := fun i hi => by
        rw [VG.Proof.Poly1305.Arm.rval_frame k4.frame hi, k3.mem, hm2]; exact hRm i hi
      refine WP.append (VG.Proof.Poly1305.Arm.multiply_ok hfit hH hR hs40 hw4' hR4 hHm) fun s5 ⟨hx5, k5⟩ => ?_
      have hs50 : s5.gpr .r0 = st := by rw [k5.gpr _ (by decide), hs40]
      refine VG.Proof.Poly1305.Arm.wp_str (off := d9Off) (a := State.addr st + BitVec.ofNat 64 16) (by decide)
        (by rw [hs50]; exact VG.Proof.Poly1305.Arm.ea hfit (off := 16) (by decide))
        (by rw [k5.wr]; exact VG.Proof.Poly1305.Arm.outSt hw4' (off := 16) (n := 4) (by decide)) fun s6 u6 => WP.block_nil ?_
      refine ⟨VG.Proof.Poly1305.Arm.col (VG.Proof.Poly1305.Arm.fold (VG.Proof.Poly1305.Arm.addE D (fun i => (VG.Proof.Poly1305.Arm.word s i).toNat) pad)) R, ⟨fun k hk => ?_, ?_⟩,
        fun k hk => VG.Proof.Poly1305.Arm.col_lt hH hR hk, ?_, ?_⟩
      · rw [u6.gpr, VG.Proof.Poly1305.Arm.yr_eq_xr k hk]; exact hx5 k (by omega_using [hk])
      · rw [u6.mem, Mem.readW_writeW_self32]; exact hx5 9 (by decide)
      · rw [VG.Proof.Poly1305.Arm.val_col, Nat.mul_mod, hv, ← Nat.mul_mod]
        refine congrArg (· % P) (congrArg (· * VG.Proof.Poly1305.Arm.val R) ?_)
        have hm := VG.Proof.Poly1305.Arm.val_mlimb (hw4 0) (hw4 1) (hw4 2) (hw4 3)
        rw [VG.Proof.Poly1305.Arm.val_addE, hm, VG.Proof.Poly1305.Arm.msgVal]
      · have k6 : VG.Proof.Poly1305.Arm.KeepsF VG.Proof.Poly1305.Arm.work [VG.Proof.Poly1305.Arm.accR (State.addr st)] s5 s6 := by
          refine ⟨fun r _ => by rw [u6.gpr], ?_, u6.rd, u6.wr, u6.sp⟩
          rw [u6.mem]
          exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (VG.Proof.Poly1305.Arm.contains_off (by decide) (by decide))
        exact k2.trans (((k3.keepsF _).mono (by simp only [VG.Proof.Poly1305.Arm.cregs, VG.Proof.Poly1305.Arm.yregs, List.mem_cons, List.not_mem_nil, or_false, VG.Proof.Poly1305.Arm.work, forall_eq_or_imp, reduceCtorEq, or_self, or_true, forall_eq, and_self])).trans (k4.trans
          ((k5.keepsF _).trans k6)))
    rw [addTop]
    simp only [List.append_assoc, List.cons_append]
    refine VG.Proof.Poly1305.Arm.wp_ldr (off := d9Off) (a := State.addr st + BitVec.ofNat 64 16) (by decide)
      (by rw [hs10]; exact VG.Proof.Poly1305.Arm.ea hfit (off := 16) (by decide)) (VG.Proof.Poly1305.Arm.inSt hsw1 (off := 16) (n := 4) (by decide))
      fun s2 u2 => VG.Proof.Poly1305.Arm.wp_add (VG.Proof.Poly1305.Arm.op2_lsr (by decide)) fun s3 u3 => ?_
    have hD9 := hD 9 (by decide)
    have v3 : (s3.gpr .r1).toNat = D 9 + (VG.Proof.Poly1305.Arm.word s 3).toNat / 2 ^ 21 := by
      have e2 : (s2.gpr .r1).toNat = D 9 := by rw [u2.gpr, k1.mem]; exact hc.2
      rw [u3.gpr, u2.other .r2 (by decide), hr2, VG.Proof.Poly1305.Arm.toNat_add_lt (by rw [e2, VG.Proof.Poly1305.Arm.toNat_shr]; have := hw4 3; omega_using [hD9, e2, this]),
        e2, VG.Proof.Poly1305.Arm.toNat_shr]
    have k3 : VG.Proof.Poly1305.Arm.KeepsF VG.Proof.Poly1305.Arm.work [VG.Proof.Poly1305.Arm.accR (State.addr st)] s s3 :=
      (k1.keepsF _).mono (by simp only [VG.Proof.Poly1305.Arm.yregs, List.mem_cons, List.not_mem_nil, or_false, VG.Proof.Poly1305.Arm.work, forall_eq_or_imp, reduceCtorEq, or_self, or_true, forall_eq, and_self]) |>.trans
        (((u2.keeps (ws := [.r1]) (by simp only [List.mem_cons, List.not_mem_nil, or_false])).trans (u3.keeps (by simp only [List.mem_cons, List.not_mem_nil, or_false]))).keepsF _ |>.mono (by simp only [List.mem_cons, List.not_mem_nil, or_false, VG.Proof.Poly1305.Arm.work, forall_eq, reduceCtorEq, or_self]))
    have m3 : s3.mem = s.mem := by rw [u3.mem, u2.mem, k1.mem]
    have c3 : ∀ j < 9, (s3.gpr (yr j)).toNat = VG.Proof.Poly1305.Arm.addE D (fun i => (VG.Proof.Poly1305.Arm.word s i).toNat) pad j := fun j hj => by
      rw [u3.other _ (VG.Proof.Poly1305.Arm.yr_ne j hj).2.1, u2.other _ (VG.Proof.Poly1305.Arm.yr_ne j hj).2.1]; exact e1 j hj
    cases pad
    · simp only [Bool.false_eq_true, ite_false, List.nil_append]
      refine rest s3 (fun j hj => ?_) k3 m3
      rcases Nat.lt_or_ge j 9 with h | h
      · exact c3 j h
      · rw [show j = 9 by omega_using [hj, h], VG.Proof.Poly1305.Arm.yr9, v3]; simp [VG.Proof.Poly1305.Arm.addE, VG.Proof.Poly1305.Arm.mlimb]
    · simp only [ite_true, List.cons_append, List.nil_append]
      refine VG.Proof.Poly1305.Arm.wp_add (VG.Proof.Poly1305.Arm.op2_imm (by decide)) fun s4 u4 => rest s4 (fun j hj => ?_)
        (k3.trans ((u4.keeps (ws := [.r1]) (by simp only [List.mem_cons, List.not_mem_nil, or_false])).keepsF _ |>.mono (by simp only [List.mem_cons, List.not_mem_nil, or_false, VG.Proof.Poly1305.Arm.work, forall_eq, reduceCtorEq, or_self]))) (by rw [u4.mem, m3])
      rcases Nat.lt_or_ge j 9 with h | h
      · rw [u4.other _ (VG.Proof.Poly1305.Arm.yr_ne j h).2.1]; exact c3 j h
      · have e2048 : (2048 : BitVec 32).toNat = 2048 := rfl
        rw [show j = 9 by omega_using [hj, h], VG.Proof.Poly1305.Arm.yr9, u4.gpr, VG.Proof.Poly1305.Arm.toNat_add_lt (by rw [v3, e2048]; have := hw4 3; omega_using [hD9, v3]), v3,
          e2048]
        simp [VG.Proof.Poly1305.Arm.addE, VG.Proof.Poly1305.Arm.mlimb]
  exact top

end

end VG.Proof.Poly1305.Arm

end

-- Formerly the module `VerifiedGarbage.Proof.Poly1305.Arm.Setup`.
section

section

/-!
# Poly1305 on 32-bit ARM: runs of stores and loads

A run of stores of registers (words, or bytes) at distinct offsets from a base
register (`stores_ok`), and a run of loads (`loads_ok`).
-/

namespace VG.Proof.Poly1305.Arm

open VG VG.Arm VG.Impl.Poly1305.Arm

/-- The store of register `r` at `[b, #o]`: a word, or a byte if `byte`. -/
def storeI (b : Reg) : Reg × Nat × Bool → Instr
  | (r, o, false) => .str r b o
  | (r, o, true) => .strb r b o

/-- The size of a store. -/
def ssize : Bool → Nat
  | false => 4
  | true => 1

/-- The bytes a store writes. -/
def sregion (B : Addr) (x : Reg × Nat × Bool) : Region := ⟨B + BitVec.ofNat 64 x.2.1, VG.Proof.Poly1305.Arm.ssize x.2.2⟩

/-- What a store leaves in memory: register `r`'s value, or its low byte, at `B + o`. -/
def Stored (B : Addr) (g : Reg → BitVec 32) (m : Mem) : Reg × Nat × Bool → Prop
  | (r, o, false) => m.readW (B + BitVec.ofNat 64 o) 32 = g r
  | (r, o, true) => m (B + BitVec.ofNat 64 o) = (g r).setWidth 8

/-- Two stores' bytes do not overlap. -/
def Apart (x y : Reg × Nat × Bool) : Prop := x.2.1 + VG.Proof.Poly1305.Arm.ssize x.2.2 ≤ y.2.1 ∨ y.2.1 + VG.Proof.Poly1305.Arm.ssize y.2.2 ≤ x.2.1

instance (x y : Reg × Nat × Bool) : Decidable (VG.Proof.Poly1305.Arm.Apart x y) := by unfold VG.Proof.Poly1305.Arm.Apart; infer_instance

theorem sregion_disjoint (B : Addr) {x y : Reg × Nat × Bool} (h : VG.Proof.Poly1305.Arm.Apart x y) (hx : x.2.1 < 2 ^ 32)
    (hy : y.2.1 < 2 ^ 32) : (VG.Proof.Poly1305.Arm.sregion B x).Disjoint (VG.Proof.Poly1305.Arm.sregion B y) := by
  obtain ⟨_, o, b⟩ := x
  obtain ⟨_, o', b'⟩ := y
  simp only [VG.Proof.Poly1305.Arm.Apart] at h hx hy
  simp only [VG.Proof.Poly1305.Arm.sregion]
  cases b <;> cases b' <;> simp only [VG.Proof.Poly1305.Arm.ssize] at h ⊢ <;> exact Offset.disjoint B h (by omega_using [hx]) (by omega_using [hy])

theorem Stored.frame {B : Addr} {g : Reg → BitVec 32} {m m' : Mem} {x : Reg × Nat × Bool}
    (h : VG.Proof.Poly1305.Arm.Stored B g m x) {F : List Region} (hf : Frame F m m')
    (hd : ∀ r ∈ F, (VG.Proof.Poly1305.Arm.sregion B x).Disjoint r) : VG.Proof.Poly1305.Arm.Stored B g m' x := by
  obtain ⟨r, o, b⟩ := x
  cases b
  · simp only [VG.Proof.Poly1305.Arm.Stored] at h ⊢
    rw [hf.readW (Region.contains_self _ _) hd (by decide)]; exact h
  · simp only [VG.Proof.Poly1305.Arm.Stored] at h ⊢
    rw [hf _ fun r' hr' hc => hd r' hr' _ (by simp only [Region.Contains, VG.Proof.Poly1305.Arm.sregion, VG.Proof.Poly1305.Arm.ssize, BitVec.sub_self, BitVec.toNat_ofNat, Nat.reducePow, Nat.zero_mod, Nat.zero_add, Std.le_refl]) hc]; exact h

theorem stores_ok (b : Reg) {B : Addr} {bv : BitVec 32} {len : Nat} (hfit : bv.toNat + len ≤ 2 ^ 32)
    (hB : B = State.addr bv) : ∀ (l : List (Reg × Nat × Bool)) (s : State),
    s.gpr b = bv → (⟨B, len⟩ : Region) ∈ s.wr → (∀ x ∈ l, x.2.1 + VG.Proof.Poly1305.Arm.ssize x.2.2 ≤ len ∧ x.2.1 < 4096) →
    l.Pairwise VG.Proof.Poly1305.Arm.Apart →
    WP isa (.block (l.map (VG.Proof.Poly1305.Arm.storeI b))) s fun s' =>
      (∀ x ∈ l, VG.Proof.Poly1305.Arm.Stored B s.gpr s'.mem x) ∧ Frame (l.map (VG.Proof.Poly1305.Arm.sregion B)) s.mem s'.mem ∧
        s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp
  | [], s, _, _, _, _ => WP.block_nil ⟨fun _ h => absurd h List.not_mem_nil, Frame.refl _ _, rfl, rfl, rfl, rfl⟩
  | x :: xs, s, hb, hw, hl, hp => by
    obtain ⟨r, o, byte⟩ := x
    have ⟨hlo, ho⟩ := hl _ List.mem_cons_self
    simp only at hlo ho
    have h1s : 1 ≤ VG.Proof.Poly1305.Arm.ssize byte := by cases byte <;> simp [VG.Proof.Poly1305.Arm.ssize]
    have ha : State.addr (s.gpr b + BitVec.ofNat 32 o) = B + BitVec.ofNat 64 o := by
      rw [hb, hB]; exact addr_add (by omega_using [hfit, hlo, h1s])
    have hc : (⟨B, len⟩ : Region).Contains (B + BitVec.ofNat 64 o) (VG.Proof.Poly1305.Arm.ssize byte) :=
      VG.Proof.Poly1305.Arm.contains_off hlo (by omega_using [ho])
    have hp' := List.pairwise_cons.mp hp
    have rest : ∀ s1 : State, VG.Proof.Poly1305.Arm.Mupd s s1 (s1.mem) → VG.Proof.Poly1305.Arm.Stored B s.gpr s1.mem (r, o, byte) →
        Frame [VG.Proof.Poly1305.Arm.sregion B (r, o, byte)] s.mem s1.mem →
        WP isa (.block (xs.map (VG.Proof.Poly1305.Arm.storeI b))) s1 fun s' =>
          (∀ x ∈ (r, o, byte) :: xs, VG.Proof.Poly1305.Arm.Stored B s.gpr s'.mem x) ∧
          Frame (((r, o, byte) :: xs).map (VG.Proof.Poly1305.Arm.sregion B)) s.mem s'.mem ∧
          s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
      intro s1 u1 hst hf1
      refine WP.mono (VG.Proof.Poly1305.Arm.stores_ok b hfit hB xs s1 (by rw [u1.gpr, hb]) (by rw [u1.wr]; exact hw)
        (fun y hy => hl y (List.mem_cons_of_mem _ hy)) hp'.2) fun s' ⟨hs', hf', hg', hrd', hwr', hsp'⟩ =>
        ⟨fun y hy => ?_, ?_, hg'.trans u1.gpr, hrd'.trans u1.rd, hwr'.trans u1.wr, hsp'.trans u1.sp⟩
      · rcases List.mem_cons.mp hy with rfl | hy
        · refine hst.frame hf' fun q hq => ?_
          obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hq
          exact VG.Proof.Poly1305.Arm.sregion_disjoint B (hp'.1 z hz) (by simp only; omega_using [ho])
            (by have := hl z (List.mem_cons_of_mem _ hz); omega_using [this])
        · rw [← u1.gpr]; exact hs' y hy
      · simp only [List.map_cons]
        refine (hf1.mono fun q hq => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; simp only [hq, List.mem_cons, List.mem_map, Prod.exists, Bool.exists_bool, true_or]).trans (hf'.mono fun q hq => by simp only [List.mem_cons, hq, or_true])
    cases byte
    · refine VG.Proof.Poly1305.Arm.wp_str (a := B + BitVec.ofNat 64 o) (by omega_using [ho]) ha ⟨_, hw, hc⟩ fun s1 u1 => rest s1
        ⟨u1.gpr, rfl, u1.rd, u1.wr, u1.sp, u1.z⟩ ?_ ?_
      · simp only [VG.Proof.Poly1305.Arm.Stored]; rw [u1.mem, Mem.readW_writeW_self32]
      · rw [u1.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    · refine VG.Proof.Poly1305.Arm.wp_strb (a := B + BitVec.ofNat 64 o) (by omega_using [ho]) ha ⟨_, hw, hc⟩ fun s1 u1 => rest s1
        ⟨u1.gpr, rfl, u1.rd, u1.wr, u1.sp, u1.z⟩ ?_ ?_
      · simp only [VG.Proof.Poly1305.Arm.Stored]; rw [u1.mem]
        simp only [Mem.writeW, Mem.write, BitVec.sub_self, BitVec.toNat_ofNat, Nat.reducePow, Nat.zero_mod, Nat.zero_lt_succ, Nat.div_self, Nat.lt_add_one, ↓reduceIte, Nat.reduceDiv, Nat.reduceMul, Nat.mul_zero, BitVec.setWidth_eq, BitVec.extractLsb'_eq_self]
      · rw [u1.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

end VG.Proof.Poly1305.Arm

end

/-!
# Poly1305 on 32-bit ARM: saving registers, the limbs of `r`, and loading the accumulator
-/

namespace VG.Proof.Poly1305.Arm

open VG VG.Arm VG.Impl.Poly1305.Arm
open VG.Spec.Poly1305 (P)

/-! ## Saving and restoring the callee-saved registers -/

/-- The registers `g` saved at `[56, 88)` of the state at `B`. -/
def Saved (B : Addr) (g : Reg → BitVec 32) (m : Mem) : Prop :=
  ∀ i < 8, m.readW (B + BitVec.ofNat 64 (56 + 4 * i)) 32 = g (savedReg i)

def saveList : List (Reg × Nat × Bool) := (List.range 8).map fun i => (savedReg i, 56 + 4 * i, false)

theorem saveRegs_eq : saveRegs = saveList.map (VG.Proof.Poly1305.Arm.storeI .r0) := rfl

/-- The saved registers' region. -/
abbrev saveR (B : Addr) : Region := ⟨B + BitVec.ofNat 64 56, 32⟩

section
variable {st : BitVec 32} (hfit : st.toNat + 128 ≤ 2 ^ 32)
include hfit

theorem saveRegs_ok {s : State} (h0 : s.gpr .r0 = st) (hw : VG.Proof.Poly1305.Arm.stR st ∈ s.wr) :
    WP isa (.block saveRegs) s fun s' => VG.Proof.Poly1305.Arm.Saved (State.addr st) s.gpr s'.mem ∧
      Frame [VG.Proof.Poly1305.Arm.saveR (State.addr st)] s.mem s'.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp := by
  rw [VG.Proof.Poly1305.Arm.saveRegs_eq]
  refine WP.mono (VG.Proof.Poly1305.Arm.stores_ok .r0 hfit rfl VG.Proof.Poly1305.Arm.saveList s h0 hw (by decide) (by decide))
    fun s' ⟨hs, hf, hg, hrd, hwr, hsp⟩ => ⟨fun i hi => ?_, hf.sub fun r hr => ?_, hg, hrd, hwr, hsp⟩
  · exact hs (savedReg i, 56 + 4 * i, false) (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have := List.mem_range.mp hi
    exact ⟨_, List.mem_singleton_self _, VG.Proof.Poly1305.Arm.sub_sub _ (by simp only; omega_using [this]) (by simp only [VG.Proof.Poly1305.Arm.ssize, Nat.reduceAdd, Nat.reduceLeDiff]; omega_using [this]) (by decide)⟩

theorem restoreRegs_ok {s : State} {g : Reg → BitVec 32} (h0 : s.gpr .r0 = st) (hw : VG.Proof.Poly1305.Arm.stR st ∈ s.wr)
    (hs : VG.Proof.Poly1305.Arm.Saved (State.addr st) g s.mem) :
    WP isa (.block restoreRegs) s fun s' => (∀ i < 8, s'.gpr (savedReg i) = g (savedReg i)) ∧
      VG.Proof.Poly1305.Arm.Keeps [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] s s' := by
  have hsr : ∀ i < 8, savedReg i ∈ [Reg.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] := by decide +kernel
  have hinj : ∀ i < 8, ∀ j < 8, savedReg i = savedReg j → i = j := by decide +kernel
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun n s' => (∀ i < n, s'.gpr (savedReg i) = g (savedReg i)) ∧
      VG.Proof.Poly1305.Arm.Keeps [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] s s')
    (fun n s' hn ⟨hl, hk⟩ => ?_) 8 (Nat.le_refl _) s ⟨fun _ h => absurd h (by omega_using [h]), Keeps.refl _ _⟩)
    fun s' h => h
  refine VG.Proof.Poly1305.Arm.wp_ldr (a := State.addr st + BitVec.ofNat 64 (56 + 4 * n)) (by omega_using [hn])
    (by rw [hk.gpr _ (by decide), h0]; exact VG.Proof.Poly1305.Arm.ea hfit (by omega_using [hn]))
    (by rw [hk.rd, hk.wr]; exact VG.Proof.Poly1305.Arm.inSt hw (by omega_using [hn])) fun s1 u1 => WP.block_nil ⟨fun i hi => ?_,
      hk.trans (u1.keeps (hsr n hn))⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h' | rfl
  · rw [u1.other _ (fun e => absurd (hinj _ (by omega_using [hn, h']) _ hn e) (by omega_using [h']))]; exact hl i h'
  · rw [u1.gpr, hk.mem]; exact hs i hn

/-! ## The limbs of `r` -/

/-- The key's words at `[24, 40)`, clamped. -/
def cw (m : Mem) (B : Addr) (i : Nat) : BitVec 32 :=
  m.readW (B + BitVec.ofNat 64 (24 + 4 * i)) 32 &&& (if i = 0 then 0x0fffffff else 0x0ffffffc)

/-- The limbs of the clamped `r` of the key in the memory `m` of the state at `B`. -/
def rlimb (m : Mem) (B : Addr) : Nat → Nat :=
  VG.Proof.Poly1305.Arm.mlimb (VG.Proof.Poly1305.Arm.cw m B 0).toNat (VG.Proof.Poly1305.Arm.cw m B 1).toNat (VG.Proof.Poly1305.Arm.cw m B 2).toNat (VG.Proof.Poly1305.Arm.cw m B 3).toNat

/-- The region `clampWords` and `setupR` write. -/
abbrev rR (B : Addr) : Region := ⟨B + BitVec.ofNat 64 88, 36⟩

omit hfit in
theorem key_rR (B : Addr) {d : Nat} (hd : d + 4 ≤ 88) :
    (⟨B + BitVec.ofNat 64 d, 4⟩ : Region).Disjoint (VG.Proof.Poly1305.Arm.rR B) :=
  Offset.disjoint B (Or.inl hd) (by omega_using [hd]) (by decide)

theorem clampWords_ok {s : State} (h0 : s.gpr .r0 = st) (hw : VG.Proof.Poly1305.Arm.stR st ∈ s.wr) :
    WP isa (.block clampWords) s fun s' =>
      (∀ i < 4, s'.mem.readW (State.addr st + BitVec.ofNat 64 (88 + 4 * i)) 32 = VG.Proof.Poly1305.Arm.cw s.mem (State.addr st) i) ∧
      VG.Proof.Poly1305.Arm.KeepsF [.r1, .r2] [VG.Proof.Poly1305.Arm.rR (State.addr st)] s s' := by
  have hkey : ∀ {m : Mem}, Frame [VG.Proof.Poly1305.Arm.rR (State.addr st)] s.mem m → ∀ i < 4,
      m.readW (State.addr st + BitVec.ofNat 64 (24 + 4 * i)) 32 =
        s.mem.readW (State.addr st + BitVec.ofNat 64 (24 + 4 * i)) 32 := fun hf i hi =>
    hf.readW (Region.contains_self _ _) (by simpa using VG.Proof.Poly1305.Arm.key_rR (State.addr st) (d := 24 + 4 * i) (by omega_using [hi]))
      (by decide)
  rw [clampWords]
  simp only [List.cons_append]
  refine VG.Proof.Poly1305.Arm.wp_movw fun s1 u1 => VG.Proof.Poly1305.Arm.wp_movt fun s2 u2 => ?_
  refine VG.Proof.Poly1305.Arm.wp_ldr (a := State.addr st + BitVec.ofNat 64 24) (by decide)
    (by rw [u2.other _ (by decide), u1.other _ (by decide), h0]; exact VG.Proof.Poly1305.Arm.ea hfit (by decide))
    (by rw [u2.rd, u2.wr, u1.rd, u1.wr]; exact VG.Proof.Poly1305.Arm.inSt hw (by decide)) fun s3 u3 => ?_
  refine VG.Proof.Poly1305.Arm.wp_and (VG.Proof.Poly1305.Arm.op2_reg _ _) fun s4 u4 => ?_
  refine VG.Proof.Poly1305.Arm.wp_str (a := State.addr st + BitVec.ofNat 64 88) (by decide)
    (by rw [u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide),
      u1.other _ (by decide), h0]; exact VG.Proof.Poly1305.Arm.ea hfit (by decide))
    (by rw [u4.wr, u3.wr, u2.wr, u1.wr]; exact VG.Proof.Poly1305.Arm.outSt hw (by decide)) fun s5 u5 => ?_
  refine VG.Proof.Poly1305.Arm.wp_movw fun s6 u6 => VG.Proof.Poly1305.Arm.wp_movt fun s7 u7 => ?_
  rw [List.nil_append]
  have v0 : s5.mem.readW (State.addr st + BitVec.ofNat 64 88) 32 = VG.Proof.Poly1305.Arm.cw s.mem (State.addr st) 0 := by
    rw [u5.mem, Mem.readW_writeW_self32, u4.gpr, u3.gpr, u3.other _ (by decide), u2.gpr, u1.gpr,
      u2.mem, u1.mem]
    rfl
  have k7 : VG.Proof.Poly1305.Arm.KeepsF [.r1, .r2] [VG.Proof.Poly1305.Arm.rR (State.addr st)] s s7 := by
    refine ⟨fun r hr => ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [u7.other _ hr.2, u6.other _ hr.2, u5.gpr, u4.other _ hr.1, u3.other _ hr.1, u2.other _ hr.2,
        u1.other _ hr.2]
    · rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (VG.Proof.Poly1305.Arm.contains_sub _ (by decide) (by decide)
        (by decide))
    · rw [u7.rd, u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd]
    · rw [u7.wr, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr]
    · rw [u7.sp, u6.sp, u5.sp, u4.sp, u3.sp, u2.sp, u1.sp]
  have m2 : s7.gpr .r2 = 0x0ffffffc := by rw [u7.gpr, u6.gpr]; rfl
  have m7 : s7.mem.readW (State.addr st + BitVec.ofNat 64 88) 32 = VG.Proof.Poly1305.Arm.cw s.mem (State.addr st) 0 := by
    rw [u7.mem, u6.mem]; exact v0
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun n s' => (∀ i < n + 1, s'.mem.readW (State.addr st + BitVec.ofNat 64 (88 + 4 * i)) 32 =
      VG.Proof.Poly1305.Arm.cw s.mem (State.addr st) i) ∧ s'.gpr .r2 = 0x0ffffffc ∧ VG.Proof.Poly1305.Arm.KeepsF [.r1, .r2] [VG.Proof.Poly1305.Arm.rR (State.addr st)] s s')
    (fun n s' hn ⟨hl, hr2, hk⟩ => ?_) 3 (Nat.le_refl _) s7 ⟨fun i hi => by rw [show i = 0 by omega_using [hi]]; exact m7,
      m2, k7⟩) fun s' ⟨hl, _, hk⟩ => ⟨hl, hk⟩
  have hs0 : s'.gpr .r0 = st := by rw [hk.gpr _ (by decide), h0]
  refine VG.Proof.Poly1305.Arm.wp_ldr (a := State.addr st + BitVec.ofNat 64 (24 + 4 * (n + 1))) (by omega_using [hn])
    (by rw [hs0, show 28 + 4 * n = 24 + 4 * (n + 1) by omega_using []]; exact VG.Proof.Poly1305.Arm.ea hfit (by omega_using [hn]))
    (by rw [hk.rd, hk.wr]; exact VG.Proof.Poly1305.Arm.inSt hw (by omega_using [hn])) fun s1 u1 => ?_
  refine VG.Proof.Poly1305.Arm.wp_and (VG.Proof.Poly1305.Arm.op2_reg _ _) fun s2 u2 => ?_
  refine VG.Proof.Poly1305.Arm.wp_str (a := State.addr st + BitVec.ofNat 64 (88 + 4 * (n + 1))) (by omega_using [hn])
    (by rw [u2.other _ (by decide), u1.other _ (by decide), hs0,
      show 92 + 4 * n = 88 + 4 * (n + 1) by omega_using []]; exact VG.Proof.Poly1305.Arm.ea hfit (by omega_using [hn]))
    (by rw [u2.wr, u1.wr, hk.wr]; exact VG.Proof.Poly1305.Arm.outSt hw (by omega_using [hn])) fun s3 u3 => WP.block_nil ⟨fun i hi => ?_, ?_, ?_⟩
  · rw [u3.mem]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h' | rfl
    · rw [VG.Proof.Poly1305.Arm.readW_writeW_off _ _ _ (by omega_using [hn, h']) (by omega_using [hn]) (by omega_using [h']), u2.mem, u1.mem]; exact hl i h'
    · rw [Mem.readW_writeW_self32, u2.gpr, u1.gpr, u1.other _ (by decide), hr2, hkey hk.frame _ (by omega_using [hn]),
        VG.Proof.Poly1305.Arm.cw, VG.Proof.Poly1305.Arm.iteF (by omega_using [hn])]
  · rw [u3.gpr, u2.other _ (by decide), u1.other _ (by decide), hr2]
  · refine hk.trans ⟨fun r hr => ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [u3.gpr, u2.other _ hr.1, u1.other _ hr.1]
    · rw [u3.mem, u2.mem, u1.mem]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (VG.Proof.Poly1305.Arm.contains_sub _ (by omega_using [hn]) (by omega_using [hn])
        (by decide))
    · rw [u3.rd, u2.rd, u1.rd]
    · rw [u3.wr, u2.wr, u1.wr]
    · rw [u3.sp, u2.sp, u1.sp]

omit hfit in
theorem zeroY_ok {s : State} :
    WP isa (.block zeroY) s fun s' => (∀ k < 9, s'.gpr (yr k) = 0) ∧ VG.Proof.Poly1305.Arm.Keeps VG.Proof.Poly1305.Arm.yregs s s' := by
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun n s' => (∀ k < n, s'.gpr (yr k) = 0) ∧ VG.Proof.Poly1305.Arm.Keeps VG.Proof.Poly1305.Arm.yregs s s')
    (fun n s' hn ⟨hz, hk⟩ => VG.Proof.Poly1305.Arm.wp_mov (VG.Proof.Poly1305.Arm.op2_imm (by decide)) fun s1 u1 => WP.block_nil ⟨fun k hk' => ?_,
      hk.trans (u1.keeps (VG.Proof.Poly1305.Arm.yr_yregs n hn))⟩) 9 (Nat.le_refl _) s ⟨fun _ h => absurd h (by omega_using [h]), Keeps.refl _ _⟩)
    fun s' h => h
  rcases Nat.lt_succ_iff_lt_or_eq.mp hk' with h' | rfl
  · rw [u1.other _ (fun e => absurd (VG.Proof.Poly1305.Arm.yr_inj _ (by omega_using [hn, h']) _ (by omega_using [hn]) e) (by omega_using [h']))]; exact hz k h'
  · rw [u1.gpr]

/-- The stores of the limbs of `r` in `setupR`. -/
def rList : List (Reg × Nat × Bool) :=
  [(.r3, 88, false), (.r4, 92, false), (.r5, 96, false), (.r6, 100, false), (.r7, 120, true),
   (.r8, 104, false), (.r9, 108, false), (.r10, 112, false), (.r11, 116, false), (.r1, 121, true)]

omit hfit in
theorem setupR_eq : setupR = clampWords ++ zeroY ++ ([.dp .add .r1 .r0 (.imm 88)] : List Instr) ++ addWords ++
    ([.mov .r1 (.shifted .r2 .lsr 21)] : List Instr) ++ rList.map (VG.Proof.Poly1305.Arm.storeI .r0) := rfl

omit hfit in
theorem cw_lt (m : Mem) (B : Addr) (i : Nat) : (VG.Proof.Poly1305.Arm.cw m B i).toNat < 2 ^ 28 := by
  simp only [VG.Proof.Poly1305.Arm.cw, BitVec.toNat_and]
  split
  · exact VG.Proof.Poly1305.Arm.and_lt (by decide)
  · exact VG.Proof.Poly1305.Arm.and_lt (by decide)

omit hfit in
theorem cw2_even (m : Mem) (B : Addr) : (VG.Proof.Poly1305.Arm.cw m B 2).toNat % 2 = 0 := by
  simp only [VG.Proof.Poly1305.Arm.cw, BitVec.toNat_and, show (2 : Nat) ≠ 0 by decide, ite_false]
  exact VG.Proof.Poly1305.Arm.and_fffffffc_mod _

omit hfit in
theorem rlimb_lt (m : Mem) (B : Addr) (i : Nat) : VG.Proof.Poly1305.Arm.rlimb m B i < 2 ^ 13 :=
  VG.Proof.Poly1305.Arm.mlimb_lt (by have := VG.Proof.Poly1305.Arm.cw_lt m B 0; omega_using [this]) (by have := VG.Proof.Poly1305.Arm.cw_lt m B 1; omega_using [this])
    (by have := VG.Proof.Poly1305.Arm.cw_lt m B 2; omega_using [this]) (by have := VG.Proof.Poly1305.Arm.cw_lt m B 3; omega_using [this]) i

theorem setupR_ok {s : State} (h0 : s.gpr .r0 = st) (hw : VG.Proof.Poly1305.Arm.stR st ∈ s.wr) :
    WP isa (.block setupR) s fun s' => (∀ i < 10, VG.Proof.Poly1305.Arm.rval s'.mem (State.addr st) i = VG.Proof.Poly1305.Arm.rlimb s.mem (State.addr st) i) ∧
      VG.Proof.Poly1305.Arm.KeepsF (.r1 :: .r2 :: .r12 :: VG.Proof.Poly1305.Arm.yregs) [VG.Proof.Poly1305.Arm.rR (State.addr st)] s s' := by
  rw [VG.Proof.Poly1305.Arm.setupR_eq]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine WP.append (VG.Proof.Poly1305.Arm.clampWords_ok hfit h0 hw) fun s1 ⟨hm1, k1⟩ => ?_
  refine WP.append VG.Proof.Poly1305.Arm.zeroY_ok fun s2 ⟨hz2, k2⟩ => ?_
  have hs20 : s2.gpr .r0 = st := by rw [k2.gpr _ (by decide), k1.gpr _ (by decide), h0]
  refine VG.Proof.Poly1305.Arm.wp_add (VG.Proof.Poly1305.Arm.op2_imm (by decide)) fun s3 u3 => ?_
  have hs3 : s3.gpr .r1 = st + 88 := by rw [u3.gpr, hs20]
  have hw3 : VG.Proof.Poly1305.Arm.stR st ∈ s3.wr := by rw [u3.wr, k2.wr, k1.wr]; exact hw
  have hwd : ∀ i < 4, State.addr (s3.gpr .r1 + BitVec.ofNat 32 (4 * i)) =
      State.addr st + BitVec.ofNat 64 (88 + 4 * i) := fun i hi => by
    rw [hs3, BitVec.add_assoc, show (88 : BitVec 32) = BitVec.ofNat 32 88 from rfl, ← BitVec.ofNat_add]
    exact VG.Proof.Poly1305.Arm.ea hfit (by omega_using [hi])
  refine WP.append (VG.Proof.Poly1305.Arm.addWords_ok fun i hi => by rw [hwd i hi]; exact VG.Proof.Poly1305.Arm.inSt hw3 (by omega_using [hi]))
    fun s4 ⟨hc4, hr4, k4⟩ => ?_
  have hword : ∀ i < 4, VG.Proof.Poly1305.Arm.word s3 i = VG.Proof.Poly1305.Arm.cw s.mem (State.addr st) i := fun i hi => by
    simp only [VG.Proof.Poly1305.Arm.word]; rw [hwd i hi, u3.mem, k2.mem]; exact hm1 i hi
  have e4 : ∀ k < 9, (s4.gpr (yr k)).toNat = VG.Proof.Poly1305.Arm.rlimb s.mem (State.addr st) k := fun k hk => by
    rw [hc4 k hk, u3.other _ (VG.Proof.Poly1305.Arm.yr_ne k hk).2.1, hz2 k hk, VG.Proof.Poly1305.Arm.zadd, VG.Proof.Poly1305.Arm.wsum_toNat _ hk, hword 0 (by decide),
      hword 1 (by decide), hword 2 (by decide), hword 3 (by decide)]
    rfl
  refine VG.Proof.Poly1305.Arm.wp_mov (VG.Proof.Poly1305.Arm.op2_lsr (by decide)) fun s5 u5 => ?_
  have e5 : (s5.gpr .r1).toNat = VG.Proof.Poly1305.Arm.rlimb s.mem (State.addr st) 9 := by
    rw [u5.gpr, VG.Proof.Poly1305.Arm.toNat_shr, hr4, hword 3 (by decide)]; rfl
  have hs50 : s5.gpr .r0 = st := by rw [u5.other _ (by decide), k4.gpr _ (by decide), u3.other _ (by decide), hs20]
  have hw5 : VG.Proof.Poly1305.Arm.stR st ∈ s5.wr := by rw [u5.wr, k4.wr]; exact hw3
  refine WP.mono (VG.Proof.Poly1305.Arm.stores_ok .r0 hfit rfl VG.Proof.Poly1305.Arm.rList s5 hs50 hw5 (by decide) (by decide))
    fun s6 ⟨hs6, hf6, hg6, hrd6, hwr6, hsp6⟩ => ⟨fun i hi => ?_, ?_⟩
  · have hr : ∀ k < 9, (s5.gpr (yr k)).toNat = VG.Proof.Poly1305.Arm.rlimb s.mem (State.addr st) k := fun k hk => by
      rw [u5.other _ (VG.Proof.Poly1305.Arm.yr_ne k hk).2.1]; exact e4 k hk
    have b4 : VG.Proof.Poly1305.Arm.rlimb s.mem (State.addr st) 4 < 2 ^ 8 := by
      have := VG.Proof.Poly1305.Arm.cw_lt s.mem (State.addr st) 1; have := VG.Proof.Poly1305.Arm.cw2_even s.mem (State.addr st)
      simp only [VG.Proof.Poly1305.Arm.rlimb, VG.Proof.Poly1305.Arm.mlimb]; omega
    have b9 : VG.Proof.Poly1305.Arm.rlimb s.mem (State.addr st) 9 < 2 ^ 8 := by
      have := VG.Proof.Poly1305.Arm.cw_lt s.mem (State.addr st) 3
      simp only [VG.Proof.Poly1305.Arm.rlimb, VG.Proof.Poly1305.Arm.mlimb]; omega_using [this]
    have w : ∀ (r : Reg) (o : Nat) (k : Nat), (r, o, false) ∈ VG.Proof.Poly1305.Arm.rList → (s5.gpr r).toNat = VG.Proof.Poly1305.Arm.rlimb s.mem (State.addr st) k →
        (s6.mem.readW (State.addr st + BitVec.ofNat 64 o) 32).toNat = VG.Proof.Poly1305.Arm.rlimb s.mem (State.addr st) k :=
      fun r o k hm hv => by have := hs6 _ hm; simp only [VG.Proof.Poly1305.Arm.Stored] at this; rw [this, hv]
    have b : ∀ (r : Reg) (o : Nat) (k : Nat), (r, o, true) ∈ VG.Proof.Poly1305.Arm.rList → (s5.gpr r).toNat = VG.Proof.Poly1305.Arm.rlimb s.mem (State.addr st) k →
        VG.Proof.Poly1305.Arm.rlimb s.mem (State.addr st) k < 2 ^ 8 →
        (s6.mem (State.addr st + BitVec.ofNat 64 o)).toNat = VG.Proof.Poly1305.Arm.rlimb s.mem (State.addr st) k :=
      fun r o k hm hv hb => by
        have := hs6 _ hm; simp only [VG.Proof.Poly1305.Arm.Stored] at this
        rw [this, BitVec.toNat_setWidth, hv, Nat.mod_eq_of_lt hb]
    obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 := by omega_using [hi]
    all_goals simp only [VG.Proof.Poly1305.Arm.rval, rOff, Nat.reduceEqDiff, or_self, or_false, false_or, ite_true,
      ite_false]
    · exact w .r3 88 0 (by decide) (hr 0 (by decide))
    · exact w .r4 92 1 (by decide) (hr 1 (by decide))
    · exact w .r5 96 2 (by decide) (hr 2 (by decide))
    · exact w .r6 100 3 (by decide) (hr 3 (by decide))
    · exact b .r7 120 4 (by decide) (hr 4 (by decide)) b4
    · exact w .r8 104 5 (by decide) (hr 5 (by decide))
    · exact w .r9 108 6 (by decide) (hr 6 (by decide))
    · exact w .r10 112 7 (by decide) (hr 7 (by decide))
    · exact w .r11 116 8 (by decide) (hr 8 (by decide))
    · exact b .r1 121 9 (by decide) e5 b9
  · refine ⟨fun r hr => ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.mem_cons, not_or] at hr
      rw [hg6, u5.other _ hr.1, k4.gpr _ (by simp only [List.mem_cons, hr.2.1, hr.2.2.1, hr.2.2.2, or_self, not_false_eq_true]), u3.other _ hr.1,
        k2.gpr _ hr.2.2.2, k1.gpr _ (by simp only [List.mem_cons, hr.1, hr.2.1, List.not_mem_nil, or_self, not_false_eq_true])]
    · have e : s5.mem = s1.mem := by rw [u5.mem, k4.mem, u3.mem, k2.mem]
      rw [e] at hf6
      refine k1.frame.trans (hf6.sub fun r hr => ?_)
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
      have hb : ∀ x ∈ VG.Proof.Poly1305.Arm.rList, 88 ≤ x.2.1 ∧ x.2.1 + VG.Proof.Poly1305.Arm.ssize x.2.2 ≤ 124 := by decide
      have := hb x hx
      exact ⟨_, List.mem_singleton_self _, VG.Proof.Poly1305.Arm.sub_sub _ this.1 (by omega_using [this]) (by decide)⟩
    · rw [hrd6, u5.rd, k4.rd, u3.rd, k2.rd, k1.rd]
    · rw [hwr6, u5.wr, k4.wr, u3.wr, k2.wr, k1.wr]
    · rw [hsp6, u5.sp, k4.sp, u3.sp, k2.sp, k1.sp]

/-! ## Loading the accumulator -/

/-- Word `i` of the state at `B`. -/
def hwd (m : Mem) (B : Addr) (i : Nat) : Nat := (m.readW (B + BitVec.ofNat 64 (4 * i)) 32).toNat

/-- The columns `loadAcc` makes of the accumulator stored in the state at `B`. -/
def accD (m : Mem) (B : Addr) : Nat → Nat := fun k =>
  if k = 9 then VG.Proof.Poly1305.Arm.hwd m B 3 / 2 ^ 21 + VG.Proof.Poly1305.Arm.hwd m B 4 % 4 * 2 ^ 11
  else VG.Proof.Poly1305.Arm.mlimb (VG.Proof.Poly1305.Arm.hwd m B 0) (VG.Proof.Poly1305.Arm.hwd m B 1) (VG.Proof.Poly1305.Arm.hwd m B 2) (VG.Proof.Poly1305.Arm.hwd m B 3) k

omit hfit in
theorem accD_lt (m : Mem) (B : Addr) (k : Nat) : VG.Proof.Poly1305.Arm.accD m B k < 2 ^ 13 := by
  have h3 : VG.Proof.Poly1305.Arm.hwd m B 3 < 2 ^ 32 := BitVec.isLt _
  simp only [VG.Proof.Poly1305.Arm.accD]
  split
  · omega_using [h3]
  · exact VG.Proof.Poly1305.Arm.mlimb_lt (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _) h3 k

omit hfit in
theorem val_accD (m : Mem) (B : Addr) :
    VG.Proof.Poly1305.Arm.val (VG.Proof.Poly1305.Arm.accD m B) = VG.Proof.Poly1305.Arm.hwd m B 0 + 2 ^ 32 * VG.Proof.Poly1305.Arm.hwd m B 1 + 2 ^ 64 * VG.Proof.Poly1305.Arm.hwd m B 2 + 2 ^ 96 * VG.Proof.Poly1305.Arm.hwd m B 3 +
      2 ^ 128 * (VG.Proof.Poly1305.Arm.hwd m B 4 % 4) := by
  have hv := VG.Proof.Poly1305.Arm.val_mlimb (w0 := VG.Proof.Poly1305.Arm.hwd m B 0) (w1 := VG.Proof.Poly1305.Arm.hwd m B 1) (w2 := VG.Proof.Poly1305.Arm.hwd m B 2) (w3 := VG.Proof.Poly1305.Arm.hwd m B 3)
    (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _)
  simp only [VG.Proof.Poly1305.Arm.val, VG.Proof.Poly1305.Arm.accD, Nat.reduceEqDiff, ite_true, ite_false] at hv ⊢
  simp only [VG.Proof.Poly1305.Arm.mlimb] at hv ⊢
  omega_using [hv]

theorem loadAcc_ok {s : State} (h0 : s.gpr .r0 = st) (hw : VG.Proof.Poly1305.Arm.stR st ∈ s.wr) :
    WP isa (.block loadAcc) s fun s' => VG.Proof.Poly1305.Arm.ColsD (VG.Proof.Poly1305.Arm.accD s.mem (State.addr st)) (State.addr st) s' ∧
      VG.Proof.Poly1305.Arm.KeepsF (.r1 :: .r2 :: .r12 :: VG.Proof.Poly1305.Arm.yregs) [VG.Proof.Poly1305.Arm.accR (State.addr st)] s s' := by
  rw [loadAcc]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine WP.append VG.Proof.Poly1305.Arm.zeroY_ok fun s1 ⟨hz1, k1⟩ => ?_
  have hs10 : s1.gpr .r0 = st := by rw [k1.gpr _ (by decide), h0]
  refine VG.Proof.Poly1305.Arm.wp_mov (VG.Proof.Poly1305.Arm.op2_reg _ _) fun s2 u2 => ?_
  have hw2 : VG.Proof.Poly1305.Arm.stR st ∈ s2.wr := by rw [u2.wr, k1.wr]; exact hw
  have hwd' : ∀ i < 4, State.addr (s2.gpr .r1 + BitVec.ofNat 32 (4 * i)) =
      State.addr st + BitVec.ofNat 64 (4 * i) := fun i hi => by
    rw [u2.gpr, hs10]; exact VG.Proof.Poly1305.Arm.ea hfit (by omega_using [hi])
  refine WP.append (VG.Proof.Poly1305.Arm.addWords_ok fun i hi => by rw [hwd' i hi]; exact VG.Proof.Poly1305.Arm.inSt hw2 (by omega_using [hi]))
    fun s3 ⟨hc3, hr3, k3⟩ => ?_
  have hword : ∀ i < 4, (VG.Proof.Poly1305.Arm.word s2 i).toNat = VG.Proof.Poly1305.Arm.hwd s.mem (State.addr st) i := fun i hi => by
    simp only [VG.Proof.Poly1305.Arm.word]; rw [hwd' i hi, u2.mem, k1.mem]; rfl
  have hs30 : s3.gpr .r0 = st := by rw [k3.gpr _ (by decide), u2.other _ (by decide), hs10]
  refine VG.Proof.Poly1305.Arm.wp_mov (VG.Proof.Poly1305.Arm.op2_lsr (by decide)) fun s4 u4 => ?_
  refine VG.Proof.Poly1305.Arm.wp_ldr (a := State.addr st + BitVec.ofNat 64 16) (by decide)
    (by rw [u4.other _ (by decide), hs30]; exact VG.Proof.Poly1305.Arm.ea hfit (off := 16) (by decide))
    (by rw [u4.rd, u4.wr, k3.rd, k3.wr]; exact VG.Proof.Poly1305.Arm.inSt hw2 (off := 16) (n := 4) (by decide)) fun s5 u5 => ?_
  refine VG.Proof.Poly1305.Arm.wp_mov (VG.Proof.Poly1305.Arm.op2_lsl (by decide)) fun s6 u6 => VG.Proof.Poly1305.Arm.wp_add (VG.Proof.Poly1305.Arm.op2_lsr (by decide)) fun s7 u7 => ?_
  have v7 : (s7.gpr .r1).toNat = VG.Proof.Poly1305.Arm.accD s.mem (State.addr st) 9 := by
    have e4 : (s4.gpr .r1).toNat = VG.Proof.Poly1305.Arm.hwd s.mem (State.addr st) 3 / 2 ^ 21 := by
      rw [u4.gpr, VG.Proof.Poly1305.Arm.toNat_shr, hr3, hword 3 (by decide)]
    have e6 : (s6.gpr .r2).toNat = VG.Proof.Poly1305.Arm.hwd s.mem (State.addr st) 4 * 2 ^ 30 % 2 ^ 32 := by
      rw [u6.gpr, u5.gpr, VG.Proof.Poly1305.Arm.toNat_shl, u4.mem, k3.mem, u2.mem, k1.mem]; rfl
    have h3 : VG.Proof.Poly1305.Arm.hwd s.mem (State.addr st) 3 < 2 ^ 32 := BitVec.isLt _
    rw [u7.gpr, u6.other _ (by decide), u5.other _ (by decide),
      VG.Proof.Poly1305.Arm.toNat_add_lt (by rw [e4, VG.Proof.Poly1305.Arm.toNat_shr, e6]; omega_using [e6, h3]), e4, VG.Proof.Poly1305.Arm.toNat_shr, e6]
    simp only [VG.Proof.Poly1305.Arm.accD, ite_true]
    omega_using [e6]
  have hs70 : s7.gpr .r0 = st := by
    rw [u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide),
      hs30]
  refine VG.Proof.Poly1305.Arm.wp_str (a := State.addr st + BitVec.ofNat 64 16) (by decide)
    (by rw [hs70]; exact VG.Proof.Poly1305.Arm.ea hfit (off := 16) (by decide))
    (by rw [u7.wr, u6.wr, u5.wr, u4.wr, k3.wr]; exact VG.Proof.Poly1305.Arm.outSt hw2 (off := 16) (n := 4) (by decide))
    fun s8 u8 => WP.block_nil ⟨⟨fun k hk => ?_, ?_⟩, ?_⟩
  · have hne := VG.Proof.Poly1305.Arm.yr_ne k hk
    rw [u8.gpr, u7.other _ hne.2.1, u6.other _ hne.2.2.1, u5.other _ hne.2.2.1, u4.other _ hne.2.1, hc3 k hk,
      u2.other _ hne.2.1, hz1 k hk, VG.Proof.Poly1305.Arm.zadd, VG.Proof.Poly1305.Arm.wsum_toNat _ hk, hword 0 (by decide), hword 1 (by decide),
      hword 2 (by decide), hword 3 (by decide)]
    simp only [VG.Proof.Poly1305.Arm.accD, VG.Proof.Poly1305.Arm.iteF (show k ≠ 9 by omega_using [hk])]
  · rw [u8.mem, Mem.readW_writeW_self32]; exact v7
  · refine ⟨fun r hr => ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.mem_cons, not_or] at hr
      rw [u8.gpr, u7.other _ hr.1, u6.other _ hr.2.1, u5.other _ hr.2.1, u4.other _ hr.1,
        k3.gpr _ (by simp only [List.mem_cons, hr.2.1, hr.2.2.1, hr.2.2.2, or_self, not_false_eq_true]), u2.other _ hr.1, k1.gpr _ hr.2.2.2]
    · rw [u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, k3.mem, u2.mem, k1.mem]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (VG.Proof.Poly1305.Arm.contains_off (by decide) (by decide))
    · rw [u8.rd, u7.rd, u6.rd, u5.rd, u4.rd, k3.rd, u2.rd, k1.rd]
    · rw [u8.wr, u7.wr, u6.wr, u5.wr, u4.wr, k3.wr, u2.wr, k1.wr]
    · rw [u8.sp, u7.sp, u6.sp, u5.sp, u4.sp, k3.sp, u2.sp, k1.sp]

end

end VG.Proof.Poly1305.Arm

end

-- Formerly the module `VerifiedGarbage.Proof.Poly1305.Arm.Bytes`.
section

/-!
# Poly1305 on 32-bit ARM: bytes and words in memory

Byte strings in memory as 32-bit little-endian words (`bytesAt_eq_of_words`,
`leNum_bytesAt_words`), the clamped `r` of a stored key as limbs
(`val_rlimb`), and regions of the state.
-/

namespace VG.Proof.Poly1305

open Spec.Poly1305

open VG.Arm in
/-- `vg_poly1305_init(state: *mut [u64; 16], key: *const [u8; 32])`. -/
def initArm : Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 128⟩
    let key : Region := ⟨State.addr (s.gpr .r1), 32⟩
    s.rd = [key] ∧ s.wr = [state] ∧ state.Disjoint key ∧
      (s.gpr .r0).toNat + 128 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 32 ≤ 2 ^ 32
  post s s' := Repr s'.mem (State.addr (s.gpr .r0)) (bytesAt s.mem (State.addr (s.gpr .r1)) 32) []
  pub s₁ s₂ := s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1

open VG.Arm in
/-- `vg_poly1305_blocks(state: *mut [u64; 16], blocks: *const [u8; 16], n:
usize)`. -/
def blocksArm : Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 128⟩
    let blocks : Region := ⟨State.addr (s.gpr .r1), 16 * (s.gpr .r2).toNat⟩
    s.rd = [blocks] ∧ s.wr = [state] ∧ state.Disjoint blocks ∧
      (s.gpr .r0).toNat + 128 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 16 * (s.gpr .r2).toNat ≤ 2 ^ 32
  post s s' := ∀ key msg, Repr s.mem (State.addr (s.gpr .r0)) key msg →
    Repr s'.mem (State.addr (s.gpr .r0)) key
      (msg ++ bytesAt s.mem (State.addr (s.gpr .r1)) (16 * (s.gpr .r2).toNat))
  pub s₁ s₂ := s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2

open VG.Arm in
/-- The 64-bit `count` argument of `update`/`finalize`, in `r2:r3` (AAPCS: the
low word in `r2`). -/
def countArm (s : Arm.State) : BitVec 64 := s.gpr .r3 ++ s.gpr .r2

open VG.Arm in
/-- `vg_poly1305_update(state: *mut [u64; 16], count: u64, data: *const u8, len:
usize, scratch: *mut [u64; 16])`: `state` in `r0`, `count` in `r2:r3`, and
`data`, `len` and `scratch` the stack arguments 0, 1 and 2. -/
def updateArm : Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 128⟩
    let data : Region := ⟨State.addr (stackArg s 0), (stackArg s 1).toNat⟩
    let scratch : Region := ⟨State.addr (stackArg s 2), 128⟩
    let args : Region := ⟨stackArgAddr s 0, 12⟩
    s.rd = [data, args] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint scratch ∧
    (s.gpr .r0).toNat + 128 ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 32 ∧
    (stackArg s 2).toNat + 128 ≤ 2 ^ 32 ∧ s.sp.toNat + 12 ≤ 2 ^ 32
  post s s' := ∀ key msg, Buffered s.mem (State.addr (s.gpr .r0)) key msg →
    VG.Proof.Poly1305.countArm s = BitVec.ofNat 64 msg.length →
    Buffered s'.mem (State.addr (s.gpr .r0)) key
      (msg ++ bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧
    stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧ stackArg s₁ 2 = stackArg s₂ 2

open VG.Arm in
/-- `vg_poly1305_finalize(state: *mut [u64; 16], count: u64, out: *mut [u8; 16],
scratch: *mut [u64; 16])`: `state` in `r0`, `count` in `r2:r3`, and `out` and
`scratch` the stack arguments 0 and 1. -/
def finalizeArm : Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 128⟩
    let out : Region := ⟨State.addr (stackArg s 0), 16⟩
    let scratch : Region := ⟨State.addr (stackArg s 1), 128⟩
    let args : Region := ⟨stackArgAddr s 0, 8⟩
    s.rd = [args] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
    (s.gpr .r0).toNat + 128 ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + 16 ≤ 2 ^ 32 ∧
    (stackArg s 1).toNat + 128 ≤ 2 ^ 32 ∧ s.sp.toNat + 8 ≤ 2 ^ 32
  post s s' := ∀ key msg, Buffered s.mem (State.addr (s.gpr .r0)) key msg →
    VG.Proof.Poly1305.countArm s = BitVec.ofNat 64 msg.length →
    bytesAt s'.mem (State.addr (stackArg s 0)) 16 = mac key msg
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧
    stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1

end VG.Proof.Poly1305

namespace VG.Proof.Poly1305.Arm

open VG VG.Arm VG.Impl.Poly1305.Arm
open VG.Spec.Poly1305 (P clamp leNum bytesAt)

/-! ## Words -/

theorem addr_toNat (a : BitVec 32) : (State.addr a).toNat = a.toNat := by
  simp only [State.addr, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (by have := a.isLt; omega)

/-- Two byte strings are equal if their words are. -/
theorem bytesAt_eq_of_words {m m' : Mem} {p q : Addr} {n : Nat}
    (h : ∀ j < n, m.readW (p + BitVec.ofNat 64 (4 * j)) 32 = m'.readW (q + BitVec.ofNat 64 (4 * j)) 32) :
    bytesAt m p (4 * n) = bytesAt m' q (4 * n) := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  have hi := List.mem_range.mp hi
  have e : ∀ a : Addr, a + BitVec.ofNat 64 i = a + BitVec.ofNat 64 (4 * (i / 4)) + BitVec.ofNat 64 (i % 4) :=
    fun a => by rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.div_add_mod]
  rw [e p, e q, Mem.readW_byte m _ (Nat.mod_lt _ (by decide)), Mem.readW_byte m' _ (Nat.mod_lt _ (by decide)),
    h _ (by omega)]

theorem leNum_bytesAt_4 (m : Mem) (p : Addr) : leNum (bytesAt m p 4) = (m.readW p 32).toNat := by
  rw [Poly1305.leNum_bytesAt_read]
  simp only [Nat.reduceMul, Mem.readW, Nat.reduceDiv, BitVec.setWidth_eq]

/-- A byte string as little-endian words. -/
theorem leNum_bytesAt_words (m : Mem) (p : Addr) : ∀ n,
    leNum (bytesAt m p (4 * n)) = VG.Proof.Poly1305.Arm.rsum (fun j => 2 ^ (32 * j) * (m.readW (p + BitVec.ofNat 64 (4 * j)) 32).toNat) n
  | 0 => by simp only [bytesAt, Nat.mul_zero, List.range_zero, List.map_nil, leNum, VG.Proof.Poly1305.Arm.rsum]
  | n + 1 => by
    rw [show 4 * (n + 1) = 4 * n + 4 by omega, Poly1305.bytesAt_add, Poly1305.leNum_append,
      Poly1305.length_bytesAt, VG.Proof.Poly1305.Arm.leNum_bytesAt_4, VG.Proof.Poly1305.Arm.leNum_bytesAt_words m p n, VG.Proof.Poly1305.Arm.rsum,
      show (256 : Nat) ^ (4 * n) = 2 ^ (32 * n) by rw [Nat.pow_mul, Nat.pow_mul]]

theorem leNum_bytesAt_16 (m : Mem) (p : Addr) :
    leNum (bytesAt m p 16) = (m.readW (p + BitVec.ofNat 64 0) 32).toNat +
      2 ^ 32 * (m.readW (p + BitVec.ofNat 64 4) 32).toNat + 2 ^ 64 * (m.readW (p + BitVec.ofNat 64 8) 32).toNat +
      2 ^ 96 * (m.readW (p + BitVec.ofNat 64 12) 32).toNat := by
  rw [show 16 = 4 * 4 from rfl, VG.Proof.Poly1305.Arm.leNum_bytesAt_words]
  simp only [VG.Proof.Poly1305.Arm.rsum, Nat.reduceMul]
  omega

theorem leNum_bytesAt_24 (m : Mem) (p : Addr) :
    leNum (bytesAt m p 24) = (m.readW (p + BitVec.ofNat 64 0) 32).toNat +
      2 ^ 32 * (m.readW (p + BitVec.ofNat 64 4) 32).toNat + 2 ^ 64 * (m.readW (p + BitVec.ofNat 64 8) 32).toNat +
      2 ^ 96 * (m.readW (p + BitVec.ofNat 64 12) 32).toNat +
      2 ^ 128 * (m.readW (p + BitVec.ofNat 64 16) 32).toNat +
      2 ^ 160 * (m.readW (p + BitVec.ofNat 64 20) 32).toNat := by
  rw [show 24 = 4 * 6 from rfl, VG.Proof.Poly1305.Arm.leNum_bytesAt_words]
  simp only [VG.Proof.Poly1305.Arm.rsum, Nat.reduceMul]
  omega

/-! ## The stored key -/

theorem off_add (B : Addr) (a d : Nat) :
    B + BitVec.ofNat 64 a + BitVec.ofNat 64 d = B + BitVec.ofNat 64 (a + d) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem take_bytesAt (m : Mem) (p : Addr) {k n : Nat} (h : k ≤ n) :
    (bytesAt m p n).take k = bytesAt m p k := by
  simp only [bytesAt, ← List.map_take, List.take_range, Nat.min_eq_left h]

theorem drop_bytesAt (m : Mem) (p : Addr) (k n : Nat) :
    (bytesAt m p (k + n)).drop k = bytesAt m (p + BitVec.ofNat 64 k) n := by
  rw [Poly1305.bytesAt_add, List.drop_left' (Poly1305.length_bytesAt _ _ _)]

/-- The number of the key's first 16 bytes, as four words at `[24, 40)` of the state. -/
theorem leNum_r (m : Mem) (B : Addr) :
    leNum (bytesAt m (B + 24) 16) = (m.readW (B + BitVec.ofNat 64 24) 32).toNat +
      2 ^ 32 * (m.readW (B + BitVec.ofNat 64 28) 32).toNat +
      2 ^ 64 * (m.readW (B + BitVec.ofNat 64 32) 32).toNat +
      2 ^ 96 * (m.readW (B + BitVec.ofNat 64 36) 32).toNat := by
  rw [VG.Proof.Poly1305.Arm.leNum_bytesAt_16, show (24 : Addr) = BitVec.ofNat 64 24 from rfl, VG.Proof.Poly1305.Arm.off_add, VG.Proof.Poly1305.Arm.off_add, VG.Proof.Poly1305.Arm.off_add, VG.Proof.Poly1305.Arm.off_add]

theorem val_rlimb (m : Mem) (B : Addr) :
    VG.Proof.Poly1305.Arm.val (VG.Proof.Poly1305.Arm.rlimb m B) = clamp (leNum (bytesAt m (B + 24) 16)) := by
  have hc : ∀ i, (VG.Proof.Poly1305.Arm.cw m B i).toNat < 2 ^ 32 := fun i => (VG.Proof.Poly1305.Arm.cw m B i).isLt
  rw [VG.Proof.Poly1305.Arm.rlimb, VG.Proof.Poly1305.Arm.val_mlimb (hc 0) (hc 1) (hc 2) (hc 3), VG.Proof.Poly1305.Arm.leNum_r,
    VG.Proof.Poly1305.Arm.clamp_words (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _)]
  simp only [VG.Proof.Poly1305.Arm.cw, BitVec.toNat_and, Nat.mul_zero, Nat.add_zero, show (1 : Nat) ≠ 0 by decide,
    show (2 : Nat) ≠ 0 by decide, show (3 : Nat) ≠ 0 by decide, ite_true, ite_false]
  rfl

theorem rlimb_frame {m m' : Mem} {B : Addr} (h : ∀ i < 4,
    m'.readW (B + BitVec.ofNat 64 (24 + 4 * i)) 32 = m.readW (B + BitVec.ofNat 64 (24 + 4 * i)) 32) :
    VG.Proof.Poly1305.Arm.rlimb m' B = VG.Proof.Poly1305.Arm.rlimb m B := by
  simp only [VG.Proof.Poly1305.Arm.rlimb, VG.Proof.Poly1305.Arm.cw, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide)]

/-! ## Regions of the state -/

theorem sub_base (p : Addr) {a len len' : Nat} (h : a + len ≤ len') (_h' : len' < 2 ^ 64) :
    Region.Sub ⟨p + BitVec.ofNat 64 a, len⟩ ⟨p, len'⟩ :=
  Offset.sub_base p h

theorem contains_base (p : Addr) {d n len : Nat} (h : d + n ≤ len) (h' : len < 2 ^ 32) :
    (⟨p, len⟩ : Region).Contains (p + BitVec.ofNat 64 d) n :=
  VG.Proof.Poly1305.Arm.contains_off h (by omega)

/-- A region inside `[B + a, B + a + la)` is disjoint from one outside it. -/
theorem disjoint_of_sub {r₁ r₂ r₁' r₂' : Region} (h : r₁'.Disjoint r₂') (h₁ : Region.Sub r₁ r₁')
    (h₂ : Region.Sub r₂ r₂') : r₁.Disjoint r₂ :=
  (h.sub_left h₁).sub_right h₂

end VG.Proof.Poly1305.Arm

end

end

/- Proofs formerly in `VerifiedGarbage.Proof.Poly1305.Arm.Blocks`. -/
section

section

/-!
# Poly1305 on 32-bit ARM: which parts of the state the code writes

Lists of ranges of the state (`offR`), the frames of writes into them, and
what they leave unchanged: the key, the saved registers, the limbs of `r` and
the stored accumulator.
-/

namespace VG.Proof.Poly1305.Arm

open VG VG.Arm VG.Impl.Poly1305.Arm
open VG.Spec.Poly1305 (P clamp leNum bytesAt)

/-- The ranges `[a, a + len)` of the state at `B`, for `(a, len)` in `l`. -/
def offR (B : Addr) (l : List (Nat × Nat)) : List Region := l.map fun p => ⟨B + BitVec.ofNat 64 p.1, p.2⟩

/-- A range disjoint from each of the ranges `l`. -/
theorem dj_offR (B : Addr) {d n : Nat} {l : List (Nat × Nat)}
    (h : (l.all fun p => d + n ≤ p.1 ∨ p.1 + p.2 ≤ d) = true)
    (hb : d + n < 2 ^ 32) (hl : (l.all fun p => p.1 + p.2 < 2 ^ 32) = true) :
    ∀ r ∈ VG.Proof.Poly1305.Arm.offR B l, (⟨B + BitVec.ofNat 64 d, n⟩ : Region).Disjoint r := by
  intro r hr
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
  have h1 := List.all_eq_true.mp h p hp
  have h2 := List.all_eq_true.mp hl p hp
  simp only [decide_eq_true_eq] at h1 h2
  exact VG.Proof.Poly1305.Arm.disjoint_sub B h1 hb h2

/-- Each of the ranges `l` is inside one of the ranges `l'`. -/
theorem sub_offR (B : Addr) {l l' : List (Nat × Nat)}
    (h : (l.all fun p => l'.any fun q => q.1 ≤ p.1 ∧ p.1 + p.2 ≤ q.1 + q.2) = true)
    (hl : (l'.all fun q => q.1 + q.2 < 2 ^ 32) = true) :
    ∀ r ∈ VG.Proof.Poly1305.Arm.offR B l, ∃ r' ∈ VG.Proof.Poly1305.Arm.offR B l', Region.Sub r r' := by
  intro r hr
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
  obtain ⟨q, hq, h1⟩ := List.any_eq_true.mp (List.all_eq_true.mp h p hp)
  have h2 := List.all_eq_true.mp hl q hq
  simp only [decide_eq_true_eq] at h1 h2
  exact ⟨_, List.mem_map.mpr ⟨q, hq, rfl⟩, VG.Proof.Poly1305.Arm.sub_sub B h1.1 h1.2 h2⟩

theorem _root_.VG.Frame.offR_sub {B : Addr} {l l' : List (Nat × Nat)} {m m' : Mem} (hf : Frame (VG.Proof.Poly1305.Arm.offR B l) m m')
    (h : (l.all fun p => l'.any fun q => q.1 ≤ p.1 ∧ p.1 + p.2 ≤ q.1 + q.2) = true)
    (hl : (l'.all fun q => q.1 + q.2 < 2 ^ 32) = true) : Frame (VG.Proof.Poly1305.Arm.offR B l') m m' :=
  hf.sub (VG.Proof.Poly1305.Arm.sub_offR B h hl)

/-- A write inside one of the ranges. -/
theorem _root_.VG.Frame.writeOff {B : Addr} {l : List (Nat × Nat)} {m m' : Mem} (hf : Frame (VG.Proof.Poly1305.Arm.offR B l) m m')
    {a len d n : Nat} (hm : (a, len) ∈ l) (h1 : a ≤ d) (h2 : d + n ≤ a + len) (h3 : a + len < 2 ^ 32)
    {w : Nat} (v : BitVec w) (hw : w / 8 = n) :
    Frame (VG.Proof.Poly1305.Arm.offR B l) m (m'.writeW (B + BitVec.ofNat 64 d) v) :=
  hf.writeW (List.mem_map.mpr ⟨_, hm, rfl⟩) v (hw ▸ VG.Proof.Poly1305.Arm.contains_sub B h1 h2 h3)

theorem offR_one (B : Addr) (a len : Nat) : VG.Proof.Poly1305.Arm.offR B [(a, len)] = [⟨B + BitVec.ofNat 64 a, len⟩] := rfl

theorem accR_offR (B : Addr) : [VG.Proof.Poly1305.Arm.accR B] = VG.Proof.Poly1305.Arm.offR B [(0, 20)] := by simp [VG.Proof.Poly1305.Arm.offR]

theorem _root_.VG.Frame.word {B : Addr} {l : List (Nat × Nat)} {m m' : Mem} (hf : Frame (VG.Proof.Poly1305.Arm.offR B l) m m') {d : Nat}
    (h : (l.all fun p => d + 4 ≤ p.1 ∨ p.1 + p.2 ≤ d) = true) (hb : d + 4 < 2 ^ 32)
    (hl : (l.all fun p => p.1 + p.2 < 2 ^ 32) = true) :
    m'.readW (B + BitVec.ofNat 64 d) 32 = m.readW (B + BitVec.ofNat 64 d) 32 :=
  hf.readW (Region.contains_self _ _) (VG.Proof.Poly1305.Arm.dj_offR B h hb hl) (by decide)

/-! ## What the writes leave -/

theorem Saved.frame {B : Addr} {g : Reg → BitVec 32} {m m' : Mem} (hs : VG.Proof.Poly1305.Arm.Saved B g m) {l : List (Nat × Nat)}
    (hf : Frame (VG.Proof.Poly1305.Arm.offR B l) m m') (h : (l.all fun p => 88 ≤ p.1 ∨ p.1 + p.2 ≤ 56) = true)
    (hl : (l.all fun p => p.1 + p.2 < 2 ^ 32) = true) : VG.Proof.Poly1305.Arm.Saved B g m' := fun i hi => by
  rw [hf.readW (Region.contains_self _ _) (fun r hr => (VG.Proof.Poly1305.Arm.dj_offR B (d := 56) (n := 32) h (by decide) hl r hr).sub_left
    (VG.Proof.Poly1305.Arm.sub_sub B (by omega_using [hi]) (by omega_using [hi]) (by decide))) (by decide)]
  exact hs i hi

theorem rval_frame' {B : Addr} {m m' : Mem} {l : List (Nat × Nat)} (hf : Frame (VG.Proof.Poly1305.Arm.offR B l) m m')
    (h : (l.all fun p => 124 ≤ p.1 ∨ p.1 + p.2 ≤ 88) = true) (hl : (l.all fun p => p.1 + p.2 < 2 ^ 32) = true)
    {i : Nat} (hi : i < 10) : VG.Proof.Poly1305.Arm.rval m' B i = VG.Proof.Poly1305.Arm.rval m B i := by
  have hro := VG.Proof.Poly1305.Arm.rOff_lt i hi
  have h88 : 88 ≤ rOff i := by
    have : ∀ i < 10, 88 ≤ rOff i := by decide +kernel
    exact this i hi
  have hd : ∀ n, rOff i + n ≤ 124 → ∀ r ∈ VG.Proof.Poly1305.Arm.offR B l, (⟨B + BitVec.ofNat 64 (rOff i), n⟩ : Region).Disjoint r :=
    fun n hn r hr => (VG.Proof.Poly1305.Arm.dj_offR B (d := 88) (n := 36) h (by decide) hl r hr).sub_left
      (VG.Proof.Poly1305.Arm.sub_sub B (by omega_using [h88]) (by omega_using [hn]) (by decide))
  have hb : ∀ i < 10, rOff i + 1 ≤ 124 := by decide +kernel
  have hw : ∀ i < 10, ¬(i = 4 ∨ i = 9) → rOff i + 4 ≤ 124 := by decide +kernel
  simp only [VG.Proof.Poly1305.Arm.rval]
  split
  · rename_i h49
    congr 1
    exact hf _ fun r hr hc => hd 1 (hb i hi) r hr _ ((Region.contains_self _ _).byte (by simp)) hc
  · rename_i h49
    rw [hf.readW (Region.contains_self _ _) (hd 4 (hw i hi h49)) (by decide)]

theorem rlimb_frame' {B : Addr} {m m' : Mem} {l : List (Nat × Nat)} (hf : Frame (VG.Proof.Poly1305.Arm.offR B l) m m')
    (h : (l.all fun p => 40 ≤ p.1 ∨ p.1 + p.2 ≤ 24) = true) (hl : (l.all fun p => p.1 + p.2 < 2 ^ 32) = true) :
    VG.Proof.Poly1305.Arm.rlimb m' B = VG.Proof.Poly1305.Arm.rlimb m B :=
  VG.Proof.Poly1305.Arm.rlimb_frame fun i hi => hf.readW (Region.contains_self _ _) (fun r hr =>
    (VG.Proof.Poly1305.Arm.dj_offR B (d := 24) (n := 16) h (by decide) hl r hr).sub_left (VG.Proof.Poly1305.Arm.sub_sub B (by omega_using [hi]) (by omega_using [hi]) (by decide)))
    (by decide)

theorem accD_frame {B : Addr} {m m' : Mem} {l : List (Nat × Nat)} (hf : Frame (VG.Proof.Poly1305.Arm.offR B l) m m')
    (h : (l.all fun p => 20 ≤ p.1) = true) (hl : (l.all fun p => p.1 + p.2 < 2 ^ 32) = true) :
    VG.Proof.Poly1305.Arm.accD m' B = VG.Proof.Poly1305.Arm.accD m B := by
  have hw : ∀ i < 5, VG.Proof.Poly1305.Arm.hwd m' B i = VG.Proof.Poly1305.Arm.hwd m B i := fun i hi => by
    simp only [VG.Proof.Poly1305.Arm.hwd]
    rw [hf.readW (Region.contains_self _ _) (fun r hr =>
      (VG.Proof.Poly1305.Arm.dj_offR B (d := 0) (n := 20) (by
        rw [List.all_eq_true] at h ⊢
        intro p hp; have := h p hp; simp only [decide_eq_true_eq] at this ⊢; omega_using [this]) (by decide) hl r hr).sub_left
      (VG.Proof.Poly1305.Arm.sub_sub B (by omega_using [hi]) (by omega_using [hi]) (by decide))) (by decide)]
  funext k
  simp only [VG.Proof.Poly1305.Arm.accD, hw 0 (by decide), hw 1 (by decide), hw 2 (by decide), hw 3 (by decide), hw 4 (by decide)]

/-- The key's bytes. -/
theorem key_frame {B : Addr} {m m' : Mem} {l : List (Nat × Nat)} (hf : Frame (VG.Proof.Poly1305.Arm.offR B l) m m')
    (h : (l.all fun p => 56 ≤ p.1 ∨ p.1 + p.2 ≤ 24) = true) (hl : (l.all fun p => p.1 + p.2 < 2 ^ 32) = true) :
    bytesAt m' (B + 24) 32 = bytesAt m (B + 24) 32 := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  have hd := VG.Proof.Poly1305.Arm.dj_offR B (d := 24) (n := 32) h (by decide) hl
  rw [show (24 : Addr) = BitVec.ofNat 64 24 from rfl] at *
  exact hf.bytes (R := ⟨B + BitVec.ofNat 64 24, 32⟩) hd (by simp) (List.mem_range.mp hi)

/-! ## The stored accumulator -/

/-- The accumulator's limbs, if it is below `p`. -/
theorem val_accD_eq {m : Mem} {B : Addr} (h : leNum (bytesAt m B 24) < P) :
    VG.Proof.Poly1305.Arm.val (VG.Proof.Poly1305.Arm.accD m B) = leNum (bytesAt m B 24) := by
  rw [VG.Proof.Poly1305.Arm.val_accD, VG.Proof.Poly1305.Arm.leNum_bytesAt_24] at *
  simp only [VG.Proof.Poly1305.Arm.hwd, Nat.mul_zero, Nat.reduceMul] at *
  simp only [P] at h
  omega_using [h]

end VG.Proof.Poly1305.Arm

end

/-!
# Poly1305 on 32-bit ARM: `blocks`

After saving the registers, storing the block pointer and count in the state,
computing the limbs of `r` and loading the accumulator as columns
(`prologue_ok`), each block is absorbed into the columns (`body_ok`); then the
columns are reduced and stored as the accumulator (`epilogue_ok`). Between
blocks (`Common`), the columns are congruent modulo `p` to the accumulator of
the blocks so far.
-/

namespace VG.Proof.Poly1305.Arm

open VG VG.Arm VG.Impl.Poly1305.Arm
open VG.Spec.Poly1305 (P clamp leNum bytesAt accumulate Repr)

section
variable (s₀ : State)
/-- The state's address. -/
abbrev stB : Addr := State.addr (s₀.gpr .r0)
/-- The limbs of the clamped `r`, and its value. -/
abbrev Rl : Nat → Nat := VG.Proof.Poly1305.Arm.rlimb s₀.mem (VG.Proof.Poly1305.Arm.stB s₀)
abbrev Rn : Nat := VG.Proof.Poly1305.Arm.val (VG.Proof.Poly1305.Arm.Rl s₀)
/-- The accumulator on entry (if it is below `p`). -/
abbrev A0 : Nat := VG.Proof.Poly1305.Arm.val (VG.Proof.Poly1305.Arm.accD s₀.mem (VG.Proof.Poly1305.Arm.stB s₀))
/-- The number of blocks, their region, and the first `i` of them. -/
abbrev nb : Nat := (s₀.gpr .r2).toNat
abbrev blR : Region := ⟨State.addr (s₀.gpr .r1), 16 * VG.Proof.Poly1305.Arm.nb s₀⟩
abbrev blks (i : Nat) : List Byte := bytesAt s₀.mem (State.addr (s₀.gpr .r1)) (16 * i)
end

/-- The ranges of the state written once the registers are saved: `[0, 24)`
and `[56, 128)`. -/
abbrev wkL : List (Nat × Nat) := [(0, 24), (56, 72)]

theorem mod_step {h X M R : Nat} (hv : h % P = X % P) :
    ((h + M) * R) % P = (R * (X + M)) % P % P := by
  rw [Nat.mod_mod, Nat.mul_comm R, Nat.mul_mod, Nat.add_mod, hv, ← Nat.add_mod, ← Nat.mul_mod]

theorem eval_ne (s : State) : isa.eval .ne s = some !s.z := rfl
theorem eval_eq (s : State) : isa.eval .eq s = some s.z := rfl

theorem ofNat_beq_zero {k : Nat} (h : k < 2 ^ 32) : (BitVec.ofNat 32 k == 0) = decide (k = 0) := by
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this
    exact hk this

theorem KeepsF.sub {ws : List Reg} {F F' : List Region} {s s' : State} (h : VG.Proof.Poly1305.Arm.KeepsF ws F s s')
    (hs : ∀ r ∈ F, ∃ r' ∈ F', Region.Sub r r') : VG.Proof.Poly1305.Arm.KeepsF ws F' s s' :=
  ⟨h.gpr, h.frame.sub hs, h.rd, h.wr, h.sp⟩

/-- The precondition of `blocks`, by field. -/
structure BPre (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.Poly1305.Arm.blR s₀]
  wr : s₀.wr = [VG.Proof.Poly1305.Arm.stR (s₀.gpr .r0)]
  st_bl : (VG.Proof.Poly1305.Arm.stR (s₀.gpr .r0)).Disjoint (VG.Proof.Poly1305.Arm.blR s₀)
  st_fit : (s₀.gpr .r0).toNat + 128 ≤ 2 ^ 32
  bl_fit : (s₀.gpr .r1).toNat + 16 * VG.Proof.Poly1305.Arm.nb s₀ ≤ 2 ^ 32

theorem BPre.of (s : State) (h : Proof.Poly1305.blocksArm.pre s) : VG.Proof.Poly1305.Arm.BPre s := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

/-- Between blocks, after `i` of them. -/
structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  keeps : VG.Proof.Poly1305.Arm.KeepsF VG.Proof.Poly1305.Arm.work (VG.Proof.Poly1305.Arm.offR (VG.Proof.Poly1305.Arm.stB s₀) VG.Proof.Poly1305.Arm.wkL) s₀ s
  saved : VG.Proof.Poly1305.Arm.Saved (VG.Proof.Poly1305.Arm.stB s₀) s₀.gpr s.mem
  r : ∀ k < 10, VG.Proof.Poly1305.Arm.rval s.mem (VG.Proof.Poly1305.Arm.stB s₀) k = VG.Proof.Poly1305.Arm.Rl s₀ k
  acc : ∃ D, VG.Proof.Poly1305.Arm.ColsD D (VG.Proof.Poly1305.Arm.stB s₀) s ∧ (∀ k < 10, D k ≤ 3564723200) ∧
    VG.Proof.Poly1305.Arm.val D % P = Poly1305.absorbAll (VG.Proof.Poly1305.Arm.Rn s₀) (VG.Proof.Poly1305.Arm.A0 s₀) (VG.Proof.Poly1305.Arm.blks s₀ i) % P

/-- The loop invariant, before block `i`. -/
structure LInv (s₀ : State) (i : Nat) (s : State) : Prop extends VG.Proof.Poly1305.Arm.Common s₀ i s where
  ptr : s.mem.readW (VG.Proof.Poly1305.Arm.stB s₀ + BitVec.ofNat 64 124) 32 = s₀.gpr .r1 + BitVec.ofNat 32 (16 * i)
  cnt : s.mem.readW (VG.Proof.Poly1305.Arm.stB s₀ + BitVec.ofNat 64 20) 32 = BitVec.ofNat 32 (VG.Proof.Poly1305.Arm.nb s₀ - i)

/-! ## A block -/

theorem blks_succ (s₀ : State) (i : Nat) :
    VG.Proof.Poly1305.Arm.blks s₀ (i + 1) = VG.Proof.Poly1305.Arm.blks s₀ i ++ bytesAt s₀.mem (State.addr (s₀.gpr .r1) + BitVec.ofNat 64 (16 * i)) 16 := by
  simp only [VG.Proof.Poly1305.Arm.blks]
  rw [show 16 * (i + 1) = 16 * i + 16 by omega_using [], Poly1305.bytesAt_add]

/-- The block's value with the `0x01` byte appended. -/
theorem leNum_pad (b : List Byte) (h : b.length = 16) : leNum (b ++ [0x01]) = leNum b + 2 ^ 128 := by
  rw [Poly1305.leNum_append, h]; rfl

theorem body_eq : body = .block (([.ldr .r1 .r0 ptrOff, .dp .add .r2 .r1 (.imm 16), .str .r2 .r0 ptrOff] : List Instr) ++
    (absorb true ++ ([.ldr .r1 .r0 cntOff, .subs .r1 .r1 (.imm 1), .str .r1 .r0 cntOff] : List Instr))) := by
  simp only [body, List.append_assoc]

theorem body_ok {s₀ : State} (hp : VG.Proof.Poly1305.Arm.BPre s₀) {i : Nat} (hi : i < VG.Proof.Poly1305.Arm.nb s₀) {s : State} (hL : VG.Proof.Poly1305.Arm.LInv s₀ i s) :
    WP isa body s fun s' =>
      (isa.eval .ne s' = some false ∧ VG.Proof.Poly1305.Arm.Common s₀ (VG.Proof.Poly1305.Arm.nb s₀) s') ∨
      (isa.eval .ne s' = some true ∧ i + 1 < VG.Proof.Poly1305.Arm.nb s₀ ∧ VG.Proof.Poly1305.Arm.LInv s₀ (i + 1) s') := by
  have hfit := hp.st_fit
  have hbf := hp.bl_fit
  have hn32 : VG.Proof.Poly1305.Arm.nb s₀ < 2 ^ 32 := (s₀.gpr .r2).isLt
  obtain ⟨D, hcD, hDb, hDv⟩ := hL.acc
  have hk := hL.keeps
  have hs0 : s.gpr .r0 = s₀.gpr .r0 := hk.gpr _ (by decide)
  have hw : VG.Proof.Poly1305.Arm.stR (s₀.gpr .r0) ∈ s.wr := by rw [hk.wr, hp.wr]; exact List.mem_singleton_self _
  rw [VG.Proof.Poly1305.Arm.body_eq, List.cons_append, List.cons_append, List.cons_append, List.nil_append]
  refine VG.Proof.Poly1305.Arm.wp_ldr (a := VG.Proof.Poly1305.Arm.stB s₀ + BitVec.ofNat 64 124) (by decide) (by rw [hs0]; exact VG.Proof.Poly1305.Arm.ea hfit (off := 124) (by decide))
    (VG.Proof.Poly1305.Arm.inSt hw (off := 124) (n := 4) (by decide)) fun s₁ u₁ => ?_
  refine VG.Proof.Poly1305.Arm.wp_add (VG.Proof.Poly1305.Arm.op2_imm (by decide)) fun s₂ u₂ => ?_
  refine VG.Proof.Poly1305.Arm.wp_str (a := VG.Proof.Poly1305.Arm.stB s₀ + BitVec.ofNat 64 124) (by decide)
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide), hs0]; exact VG.Proof.Poly1305.Arm.ea hfit (off := 124) (by decide))
    (by rw [u₂.wr, u₁.wr]; exact VG.Proof.Poly1305.Arm.outSt hw (off := 124) (n := 4) (by decide)) fun s₃ u₃ => ?_
  -- The state before `absorb`.
  have hptr : s₃.gpr .r1 = s₀.gpr .r1 + BitVec.ofNat 32 (16 * i) := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.gpr, hL.ptr]
  have m₃ : s₃.mem = s.mem.writeW (VG.Proof.Poly1305.Arm.stB s₀ + BitVec.ofNat 64 124) (s₀.gpr .r1 + BitVec.ofNat 32 (16 * (i + 1))) := by
    have e : BitVec.ofNat 32 (16 * i) + 16 = BitVec.ofNat 32 (16 * (i + 1)) := by
      rw [show 16 * (i + 1) = 16 * i + 16 by omega_using [], BitVec.ofNat_add]; rfl
    rw [u₃.mem, u₂.gpr, u₁.gpr, u₂.mem, u₁.mem, hL.ptr, BitVec.add_assoc, e]
  have f₃ : Frame (VG.Proof.Poly1305.Arm.offR (VG.Proof.Poly1305.Arm.stB s₀) [(124, 4)]) s.mem s₃.mem := by
    rw [m₃]; exact Frame.writeOff (Frame.refl _ _) (a := 124) (len := 4) (List.mem_singleton_self _) (Nat.le_refl _) (Nat.le_refl _)
      (by decide) _ rfl
  have k₃ : VG.Proof.Poly1305.Arm.KeepsF [.r1, .r2] (VG.Proof.Poly1305.Arm.offR (VG.Proof.Poly1305.Arm.stB s₀) [(124, 4)]) s s₃ :=
    ⟨fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [u₃.gpr, u₂.other _ hr.2, u₁.other _ hr.1],
      f₃, by rw [u₃.rd, u₂.rd, u₁.rd], by rw [u₃.wr, u₂.wr, u₁.wr], by rw [u₃.sp, u₂.sp, u₁.sp]⟩
  have hs30 : s₃.gpr .r0 = s₀.gpr .r0 := by rw [k₃.gpr _ (by decide), hs0]
  have hw₃ : VG.Proof.Poly1305.Arm.stR (s₀.gpr .r0) ∈ s₃.wr := by rw [k₃.wr]; exact hw
  have hR₃ : ∀ k < 10, VG.Proof.Poly1305.Arm.rval s₃.mem (VG.Proof.Poly1305.Arm.stB s₀) k = VG.Proof.Poly1305.Arm.Rl s₀ k := fun k hk' => by
    rw [VG.Proof.Poly1305.Arm.rval_frame' f₃ (by decide) (by decide) hk']; exact hL.r k hk'
  have hc₃ : VG.Proof.Poly1305.Arm.ColsD D (VG.Proof.Poly1305.Arm.stB s₀) s₃ := ⟨fun k hk' => by
      have := VG.Proof.Poly1305.Arm.yr_ne k hk'
      rw [k₃.gpr _ (by simp [this.2.1, this.2.2.1])]; exact hcD.1 k hk',
    by rw [f₃.word (by decide) (by decide) (by decide)]; exact hcD.2⟩
  -- The block.
  have hbA : ∀ j < 4, State.addr (s₃.gpr .r1 + BitVec.ofNat 32 (4 * j)) =
      State.addr (s₀.gpr .r1) + BitVec.ofNat 64 (16 * i + 4 * j) := fun j hj => by
    rw [hptr, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact addr_add (a := s₀.gpr .r1) (k := 16 * i + 4 * j) (by omega_using [hi, hbf, hj])
  have hin : ∀ j < 4, InRegions (s₃.rd ++ s₃.wr) (State.addr (s₃.gpr .r1 + BitVec.ofNat 32 (4 * j))) 4 :=
    fun j hj => by
      rw [hbA j hj, k₃.rd, hk.rd, hp.rd]
      exact ⟨_, List.mem_append_left _ (List.mem_singleton_self _),
        VG.Proof.Poly1305.Arm.contains_off (off := 16 * i + 4 * j) (n := 4) (len := 16 * VG.Proof.Poly1305.Arm.nb s₀) (by omega_using [hi, hj]) (by omega_using [hi, hn32, hj])⟩
  have hfr : Frame [VG.Proof.Poly1305.Arm.stR (s₀.gpr .r0)] s₀.mem s₃.mem :=
    (hk.frame.trans (f₃.offR_sub (l' := VG.Proof.Poly1305.Arm.wkL) (by decide) (by decide))).sub fun r hr => by
      obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hr
      simp only [VG.Proof.Poly1305.Arm.wkL, List.mem_cons, List.not_mem_nil, or_false] at hp'
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      rcases hp' with rfl | rfl
      · exact VG.Proof.Poly1305.Arm.sub_base _ (by decide) (by decide)
      · exact VG.Proof.Poly1305.Arm.sub_base _ (by decide) (by decide)
  have hmsg : VG.Proof.Poly1305.Arm.msgVal s₃ = leNum (bytesAt s₀.mem (State.addr (s₀.gpr .r1) + BitVec.ofNat 64 (16 * i)) 16) := by
    have e : ∀ j < 4, (VG.Proof.Poly1305.Arm.word s₃ j).toNat =
        (s₀.mem.readW (State.addr (s₀.gpr .r1) + BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 (4 * j)) 32).toNat :=
      fun j hj => by
        simp only [VG.Proof.Poly1305.Arm.word]
        rw [hbA j hj, VG.Proof.Poly1305.Arm.off_add, hfr.readW (Region.contains_self _ _) (by
          simp only [List.mem_singleton, forall_eq]
          exact (hp.st_bl.sub_right (VG.Proof.Poly1305.Arm.sub_base _ (by omega_using [hi, hj]) (by omega_using [hn32]))).symm) (by decide)]
    rw [VG.Proof.Poly1305.Arm.leNum_bytesAt_16, VG.Proof.Poly1305.Arm.msgVal, e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide)]
  rw [← List.append_nil [Instr.ldr .r1 .r0 cntOff, .subs .r1 .r1 (.imm 1), .str .r1 .r0 cntOff]]
  refine WP.append (VG.Proof.Poly1305.Arm.absorb_ok hfit true (fun i hi => VG.Proof.Poly1305.Arm.rlimb_lt _ _ i) hDb hs30 hw₃ hR₃ hc₃ hin)
    fun s₄ ⟨D', hc₄, hb₄, hv₄, k₄⟩ => ?_
  have hs40 : s₄.gpr .r0 = s₀.gpr .r0 := by rw [k₄.gpr _ (by decide), hs30]
  have hw₄ : VG.Proof.Poly1305.Arm.stR (s₀.gpr .r0) ∈ s₄.wr := by rw [k₄.wr]; exact hw₃
  have f₄ : Frame (VG.Proof.Poly1305.Arm.offR (VG.Proof.Poly1305.Arm.stB s₀) [(0, 20)]) s₃.mem s₄.mem := by rw [← VG.Proof.Poly1305.Arm.accR_offR]; exact k₄.frame
  refine VG.Proof.Poly1305.Arm.wp_ldr (a := VG.Proof.Poly1305.Arm.stB s₀ + BitVec.ofNat 64 20) (by decide) (by rw [hs40]; exact VG.Proof.Poly1305.Arm.ea hfit (off := 20) (by decide))
    (VG.Proof.Poly1305.Arm.inSt hw₄ (off := 20) (n := 4) (by decide)) fun s₅ u₅ => ?_
  refine VG.Proof.Poly1305.Arm.wp_subs (VG.Proof.Poly1305.Arm.op2_imm (by decide)) fun s₆ u₆ hz₆ => ?_
  refine VG.Proof.Poly1305.Arm.wp_str (a := VG.Proof.Poly1305.Arm.stB s₀ + BitVec.ofNat 64 20) (by decide)
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), hs40]; exact VG.Proof.Poly1305.Arm.ea hfit (off := 20) (by decide))
    (by rw [u₆.wr, u₅.wr]; exact VG.Proof.Poly1305.Arm.outSt hw₄ (off := 20) (n := 4) (by decide)) fun s₇ u₇ => WP.block_nil ?_
  -- The count.
  have hc₅ : s₅.gpr .r1 = BitVec.ofNat 32 (VG.Proof.Poly1305.Arm.nb s₀ - i) := by
    rw [u₅.gpr, f₄.word (by decide) (by decide) (by decide), f₃.word (by decide) (by decide) (by decide), hL.cnt]
  have hc₆ : s₆.gpr .r1 = BitVec.ofNat 32 (VG.Proof.Poly1305.Arm.nb s₀ - (i + 1)) := by
    rw [u₆.gpr, hc₅, show VG.Proof.Poly1305.Arm.nb s₀ - i = (VG.Proof.Poly1305.Arm.nb s₀ - (i + 1)) + 1 by omega_using [hi], BitVec.ofNat_add]
    exact BitVec.add_sub_cancel _ _
  have hz : s₇.z = decide (VG.Proof.Poly1305.Arm.nb s₀ - (i + 1) = 0) := by
    rw [u₇.z, hz₆, ← u₆.gpr, hc₆, VG.Proof.Poly1305.Arm.ofNat_beq_zero (by omega_using [hi, hbf, hn32])]
  have m₇ : s₇.mem = s₄.mem.writeW (VG.Proof.Poly1305.Arm.stB s₀ + BitVec.ofNat 64 20) (BitVec.ofNat 32 (VG.Proof.Poly1305.Arm.nb s₀ - (i + 1))) := by
    rw [u₇.mem, hc₆, u₆.mem, u₅.mem]
  have f₇ : Frame (VG.Proof.Poly1305.Arm.offR (VG.Proof.Poly1305.Arm.stB s₀) [(0, 24), (124, 4)]) s.mem s₇.mem := by
    rw [m₇]
    refine Frame.writeOff ((f₃.offR_sub (by decide) (by decide)).trans (f₄.offR_sub (by decide) (by decide)))
      (a := 0) (len := 24) (by decide) (by decide) (by decide) (by decide) _ rfl
  have k₇ : VG.Proof.Poly1305.Arm.KeepsF VG.Proof.Poly1305.Arm.work (VG.Proof.Poly1305.Arm.offR (VG.Proof.Poly1305.Arm.stB s₀) [(0, 24), (124, 4)]) s s₇ := by
    refine ⟨fun r hr => ?_, f₇, by rw [u₇.rd, u₆.rd, u₅.rd, k₄.rd, k₃.rd], by rw [u₇.wr, u₆.wr, u₅.wr, k₄.wr, k₃.wr],
      by rw [u₇.sp, u₆.sp, u₅.sp, k₄.sp, k₃.sp]⟩
    have h1 : r ≠ .r1 := by rintro rfl; exact hr (by decide)
    have h2 : r ≠ .r2 := by rintro rfl; exact hr (by decide)
    rw [u₇.gpr, u₆.other _ h1, u₅.other _ h1, k₄.gpr _ hr, k₃.gpr _ (by simp [h1, h2])]
  have hC : VG.Proof.Poly1305.Arm.Common s₀ (i + 1) s₇ := by
    refine ⟨hk.trans (k₇.sub (VG.Proof.Poly1305.Arm.sub_offR _ (by decide) (by decide))), hL.saved.frame f₇ (by decide) (by decide),
      fun k hk' => by rw [VG.Proof.Poly1305.Arm.rval_frame' f₇ (by decide) (by decide) hk']; exact hL.r k hk', D', ⟨fun k hk' => ?_, ?_⟩,
      hb₄, ?_⟩
    · have := VG.Proof.Poly1305.Arm.yr_ne k hk'
      rw [u₇.gpr, u₆.other _ this.2.1, u₅.other _ this.2.1]; exact hc₄.1 k hk'
    · rw [m₇, VG.Proof.Poly1305.Arm.readW_writeW_off _ _ _ (by decide) (by decide) (by decide)]; exact hc₄.2
    · have h16 : (VG.Proof.Poly1305.Arm.blks s₀ i).length % 16 = 0 := by simp only [VG.Proof.Poly1305.Arm.blks, Poly1305.length_bytesAt]; omega_using []
      have hl := Poly1305.length_bytesAt s₀.mem (State.addr (s₀.gpr .r1) + BitVec.ofNat 64 (16 * i)) 16
      rw [VG.Proof.Poly1305.Arm.blks_succ, Poly1305.absorbAll_append h16, Poly1305.absorbAll_block (by omega_using [hl]) (by omega_using [hl]), hv₄, hmsg,
        VG.Proof.Poly1305.Arm.leNum_pad _ hl, VG.Proof.Poly1305.Arm.iteT rfl, Nat.add_assoc]
      exact VG.Proof.Poly1305.Arm.mod_step hDv
  by_cases hlast : i + 1 = VG.Proof.Poly1305.Arm.nb s₀
  · refine .inl ⟨by rw [VG.Proof.Poly1305.Arm.eval_ne, hz, hlast]; simp, hlast ▸ hC⟩
  · refine .inr ⟨by rw [VG.Proof.Poly1305.Arm.eval_ne, hz]; simp; omega_using [hi, hlast], by omega_using [hi, hlast], { hC with
                                                                                                           ptr := ?_, cnt := ?_ }⟩
    · rw [m₇, VG.Proof.Poly1305.Arm.readW_writeW_off _ _ _ (by decide) (by decide) (by decide),
        f₄.word (by decide) (by decide) (by decide), m₃, Mem.readW_writeW_self32]
    · rw [m₇, Mem.readW_writeW_self32]

/-! ## Setup -/

section
variable {st : BitVec 32} (hfit : st.toNat + 128 ≤ 2 ^ 32)
include hfit

/-- The limbs of `r` and the accumulator's columns, from the state's key and accumulator. -/
theorem setupAcc_ok {s : State} (h0 : s.gpr .r0 = st) (hw : VG.Proof.Poly1305.Arm.stR st ∈ s.wr) :
    WP isa (.block (setupR ++ loadAcc)) s fun s' =>
      (∀ k < 10, VG.Proof.Poly1305.Arm.rval s'.mem (State.addr st) k = VG.Proof.Poly1305.Arm.rlimb s.mem (State.addr st) k) ∧
      VG.Proof.Poly1305.Arm.ColsD (VG.Proof.Poly1305.Arm.accD s.mem (State.addr st)) (State.addr st) s' ∧
      VG.Proof.Poly1305.Arm.KeepsF (.r1 :: .r2 :: .r12 :: VG.Proof.Poly1305.Arm.yregs) (VG.Proof.Poly1305.Arm.offR (State.addr st) [(0, 20), (88, 36)]) s s' := by
  refine WP.append (VG.Proof.Poly1305.Arm.setupR_ok hfit h0 hw) fun s₁ ⟨hr₁, k₁⟩ => ?_
  have f₁ : Frame (VG.Proof.Poly1305.Arm.offR (State.addr st) [(88, 36)]) s.mem s₁.mem := k₁.frame
  refine WP.mono (VG.Proof.Poly1305.Arm.loadAcc_ok hfit (by rw [k₁.gpr _ (by decide), h0]) (by rw [k₁.wr]; exact hw))
    fun s₂ ⟨hc₂, k₂⟩ => ⟨fun k hk => ?_, ?_, ?_⟩
  · rw [VG.Proof.Poly1305.Arm.rval_frame k₂.frame hk]; exact hr₁ k hk
  · rw [← VG.Proof.Poly1305.Arm.accD_frame f₁ (by decide) (by decide)]; exact hc₂
  · have k₁' : VG.Proof.Poly1305.Arm.KeepsF (.r1 :: .r2 :: .r12 :: VG.Proof.Poly1305.Arm.yregs) (VG.Proof.Poly1305.Arm.offR (State.addr st) [(88, 36)]) s s₁ := k₁
    refine (k₁'.sub (VG.Proof.Poly1305.Arm.sub_offR _ (l' := [(0, 20), (88, 36)]) (by decide) (by decide))).trans ?_
    have := k₂.sub (F' := VG.Proof.Poly1305.Arm.offR (State.addr st) [(0, 20), (88, 36)]) (by
      rw [VG.Proof.Poly1305.Arm.accR_offR]; exact VG.Proof.Poly1305.Arm.sub_offR _ (by decide) (by decide))
    exact this

/-- Reducing the columns fully (see `reduceRegs`). -/
theorem reduce_ok {D : Nat → Nat} (hD : ∀ k < 10, D k ≤ 3564723200) {s : State} (h0 : s.gpr .r0 = st)
    (hw : VG.Proof.Poly1305.Arm.stR st ∈ s.wr) (hc : VG.Proof.Poly1305.Arm.ColsD D (State.addr st) s) :
    WP isa (.block reduce) s fun s' => VG.Proof.Poly1305.Arm.Cols (VG.Proof.Poly1305.Arm.redL D) s' ∧ VG.Proof.Poly1305.Arm.Keeps (.r2 :: .r12 :: VG.Proof.Poly1305.Arm.cregs) s s' := by
  rw [reduce]
  refine VG.Proof.Poly1305.Arm.wp_ldr (a := State.addr st + BitVec.ofNat 64 16) (by decide) (by rw [h0]; exact VG.Proof.Poly1305.Arm.ea hfit (off := 16) (by decide))
    (VG.Proof.Poly1305.Arm.inSt hw (off := 16) (n := 4) (by decide)) fun s₁ u₁ => ?_
  have hc₁ : VG.Proof.Poly1305.Arm.Cols D s₁ := fun j hj => by
    rcases Nat.lt_or_ge j 9 with h | h
    · rw [u₁.other _ (VG.Proof.Poly1305.Arm.yr_ne j h).2.1]; exact hc.1 j h
    · rw [show j = 9 by omega_using [hj, h], VG.Proof.Poly1305.Arm.yr9, u₁.gpr]; exact hc.2
  refine WP.mono (VG.Proof.Poly1305.Arm.reduceRegs_ok (fun j hj => by have := hD j hj; omega_using [this]) hc₁) fun s₂ ⟨hc₂, _, k₂⟩ =>
    ⟨hc₂, (u₁.keeps (by simp [VG.Proof.Poly1305.Arm.cregs])).trans k₂⟩

end

/-! ## Prologue -/

theorem blks_zero (s₀ : State) : VG.Proof.Poly1305.Arm.blks s₀ 0 = [] := by simp [VG.Proof.Poly1305.Arm.blks, bytesAt]

theorem prologue_ok {s₀ : State} (hp : VG.Proof.Poly1305.Arm.BPre s₀) :
    WP isa (.block (saveRegs ++ ([.str .r1 .r0 ptrOff, .str .r2 .r0 cntOff] : List Instr) ++ setupR ++ loadAcc ++
      ([.ldr .r1 .r0 cntOff, .cmp .r1 (.imm 0)] : List Instr))) s₀ fun s =>
      VG.Proof.Poly1305.Arm.LInv s₀ 0 s ∧ s.z = (s₀.gpr .r2 == 0) := by
  have hfit := hp.st_fit
  have hw : VG.Proof.Poly1305.Arm.stR (s₀.gpr .r0) ∈ s₀.wr := by rw [hp.wr]; exact List.mem_singleton_self _
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine WP.append (VG.Proof.Poly1305.Arm.saveRegs_ok hfit rfl hw) fun s₁ ⟨hsv, hf₁, hg₁, hrd₁, hwr₁, hsp₁⟩ => ?_
  have hw₁ : VG.Proof.Poly1305.Arm.stR (s₀.gpr .r0) ∈ s₁.wr := by rw [hwr₁]; exact hw
  refine VG.Proof.Poly1305.Arm.wp_str (a := VG.Proof.Poly1305.Arm.stB s₀ + BitVec.ofNat 64 124) (by decide)
    (by rw [hg₁]; exact VG.Proof.Poly1305.Arm.ea hfit (off := 124) (by decide)) (VG.Proof.Poly1305.Arm.outSt hw₁ (off := 124) (n := 4) (by decide))
    fun s₂ u₂ => ?_
  refine VG.Proof.Poly1305.Arm.wp_str (a := VG.Proof.Poly1305.Arm.stB s₀ + BitVec.ofNat 64 20) (by decide)
    (by rw [u₂.gpr, hg₁]; exact VG.Proof.Poly1305.Arm.ea hfit (off := 20) (by decide))
    (by rw [u₂.wr]; exact VG.Proof.Poly1305.Arm.outSt hw₁ (off := 20) (n := 4) (by decide)) fun s₃ u₃ => ?_
  have m₃ : s₃.mem = (s₁.mem.writeW (VG.Proof.Poly1305.Arm.stB s₀ + BitVec.ofNat 64 124) (s₀.gpr .r1)).writeW
      (VG.Proof.Poly1305.Arm.stB s₀ + BitVec.ofNat 64 20) (s₀.gpr .r2) := by rw [u₃.mem, u₂.mem, u₂.gpr, hg₁]
  have f₁₃ : Frame (VG.Proof.Poly1305.Arm.offR (VG.Proof.Poly1305.Arm.stB s₀) [(20, 4), (124, 4)]) s₁.mem s₃.mem := by
    rw [m₃]
    exact Frame.writeOff (Frame.writeOff (Frame.refl _ _) (a := 124) (len := 4) (by decide) (Nat.le_refl _) (Nat.le_refl _)
      (by decide) _ rfl) (a := 20) (len := 4) (by decide) (Nat.le_refl _) (Nat.le_refl _) (by decide) _ rfl
  have hs₃0 : s₃.gpr .r0 = s₀.gpr .r0 := by rw [u₃.gpr, u₂.gpr, hg₁]
  have hw₃ : VG.Proof.Poly1305.Arm.stR (s₀.gpr .r0) ∈ s₃.wr := by rw [u₃.wr, u₂.wr]; exact hw₁
  rw [← List.append_assoc setupR loadAcc]
  refine WP.append (VG.Proof.Poly1305.Arm.setupAcc_ok hfit hs₃0 hw₃) fun s₄ ⟨hr₄, hc₄, k₄⟩ => ?_
  have hs₄0 : s₄.gpr .r0 = s₀.gpr .r0 := by rw [k₄.gpr _ (by decide), hs₃0]
  have hw₄ : VG.Proof.Poly1305.Arm.stR (s₀.gpr .r0) ∈ s₄.wr := by rw [k₄.wr]; exact hw₃
  refine VG.Proof.Poly1305.Arm.wp_ldr (a := VG.Proof.Poly1305.Arm.stB s₀ + BitVec.ofNat 64 20) (by decide)
    (by rw [hs₄0]; exact VG.Proof.Poly1305.Arm.ea hfit (off := 20) (by decide)) (VG.Proof.Poly1305.Arm.inSt hw₄ (off := 20) (n := 4) (by decide))
    fun s₅ u₅ => VG.Proof.Poly1305.Arm.wp_cmp (VG.Proof.Poly1305.Arm.op2_imm (by decide)) fun s₆ u₆ hz => WP.block_nil ?_
  have f₀₁ : Frame (VG.Proof.Poly1305.Arm.offR (VG.Proof.Poly1305.Arm.stB s₀) [(56, 32)]) s₀.mem s₁.mem := hf₁
  have f₁₄ : Frame (VG.Proof.Poly1305.Arm.offR (VG.Proof.Poly1305.Arm.stB s₀) [(0, 20), (20, 4), (88, 36), (124, 4)]) s₁.mem s₄.mem :=
    (f₁₃.offR_sub (by decide) (by decide)).trans (k₄.frame.offR_sub (by decide) (by decide))
  have m₆ : s₆.mem = s₄.mem := by rw [u₆.mem, u₅.mem]
  -- The key and the stored accumulator on entry.
  have f₀₃ : Frame (VG.Proof.Poly1305.Arm.offR (VG.Proof.Poly1305.Arm.stB s₀) [(20, 4), (56, 32), (124, 4)]) s₀.mem s₃.mem :=
    (f₀₁.offR_sub (by decide) (by decide)).trans (f₁₃.offR_sub (by decide) (by decide))
  have hRl : VG.Proof.Poly1305.Arm.rlimb s₃.mem (VG.Proof.Poly1305.Arm.stB s₀) = VG.Proof.Poly1305.Arm.Rl s₀ := VG.Proof.Poly1305.Arm.rlimb_frame' f₀₃ (by decide) (by decide)
  have hA : VG.Proof.Poly1305.Arm.accD s₃.mem (VG.Proof.Poly1305.Arm.stB s₀) = VG.Proof.Poly1305.Arm.accD s₀.mem (VG.Proof.Poly1305.Arm.stB s₀) := VG.Proof.Poly1305.Arm.accD_frame f₀₃ (by decide) (by decide)
  have hptr : s₄.mem.readW (VG.Proof.Poly1305.Arm.stB s₀ + BitVec.ofNat 64 124) 32 = s₀.gpr .r1 := by
    rw [k₄.frame.word (by decide) (by decide) (by decide), m₃,
      VG.Proof.Poly1305.Arm.readW_writeW_off _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  have hcnt : s₄.mem.readW (VG.Proof.Poly1305.Arm.stB s₀ + BitVec.ofNat 64 20) 32 = s₀.gpr .r2 := by
    rw [k₄.frame.word (by decide) (by decide) (by decide), m₃, Mem.readW_writeW_self32]
  refine ⟨⟨⟨⟨fun r hr => ?_, ?_, ?_, ?_, ?_⟩, ?_, fun k hk => ?_, VG.Proof.Poly1305.Arm.accD s₀.mem (VG.Proof.Poly1305.Arm.stB s₀), ⟨fun k hk => ?_, ?_⟩,
    fun k _ => by have := VG.Proof.Poly1305.Arm.accD_lt s₀.mem (VG.Proof.Poly1305.Arm.stB s₀) k; omega_using [this], by rw [VG.Proof.Poly1305.Arm.blks_zero, Poly1305.absorbAll_nil]⟩, ?_, ?_⟩, ?_⟩
  · have h1 : r ≠ .r1 := by rintro rfl; exact hr (by decide)
    rw [u₆.gpr, u₅.other _ h1, k₄.gpr _ (by
      simp only [VG.Proof.Poly1305.Arm.yregs, List.mem_cons, List.not_mem_nil, or_false, not_or]
      refine ⟨h1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rintro rfl <;> exact hr (by decide)),
      u₃.gpr, u₂.gpr, hg₁]
  · rw [m₆]
    exact (f₀₁.offR_sub (by decide) (by decide)).trans (f₁₄.offR_sub (by decide) (by decide))
  · rw [u₆.rd, u₅.rd, k₄.rd, u₃.rd, u₂.rd, hrd₁]
  · rw [u₆.wr, u₅.wr, k₄.wr, u₃.wr, u₂.wr, hwr₁]
  · rw [u₆.sp, u₅.sp, k₄.sp, u₃.sp, u₂.sp, hsp₁]
  · rw [m₆]; exact hsv.frame f₁₄ (by decide) (by decide)
  · rw [m₆, ← hRl]; exact hr₄ k hk
  · have := VG.Proof.Poly1305.Arm.yr_ne k hk
    rw [u₆.gpr, u₅.other _ this.2.1, ← hA]; exact hc₄.1 k hk
  · rw [m₆, ← hA]; exact hc₄.2
  · rw [m₆, hptr]; simp
  · rw [m₆, hcnt]; simp [VG.Proof.Poly1305.Arm.nb]
  · rw [hz, u₅.gpr, hcnt]; simp

/-! ## Epilogue -/

/-- The stores of the accumulator's first five words. -/
def accList : List (Reg × Nat × Bool) :=
  [(.r3, 0, false), (.r5, 4, false), (.r7, 8, false), (.r10, 12, false), (.r1, 16, false)]

theorem epi_eq : [Instr.str .r3 .r0 0, .str .r5 .r0 4, .str .r7 .r0 8, .str .r10 .r0 12, .str .r1 .r0 16,
    .mov .r2 (.imm 0), .str .r2 .r0 20] ++ restoreRegs =
    accList.map (VG.Proof.Poly1305.Arm.storeI .r0) ++ (.mov .r2 (.imm 0) :: .str .r2 .r0 20 :: restoreRegs) := rfl

theorem accList_frame (B : Addr) : accList.map (VG.Proof.Poly1305.Arm.sregion B) = VG.Proof.Poly1305.Arm.offR B [(0, 4), (4, 4), (8, 4), (12, 4), (16, 4)] :=
  rfl

theorem preserved_cases : ∀ r ∈ preserved, r = .lr ∨ ∃ i < 8, savedReg i = r := by decide

/-- The accumulator's words as a number. -/
theorem val_words {L : Nat → Nat} (hL : ∀ j < 9, L j < 2 ^ 13) :
    VG.Proof.Poly1305.Arm.tw0 L + 2 ^ 32 * VG.Proof.Poly1305.Arm.tw1 L + 2 ^ 64 * VG.Proof.Poly1305.Arm.tw2 L + 2 ^ 96 * VG.Proof.Poly1305.Arm.tw3 L + 2 ^ 128 * (L 9 / 2 ^ 11) + 2 ^ 160 * 0 =
      VG.Proof.Poly1305.Arm.val L := by
  rw [VG.Proof.Poly1305.Arm.val_toWords hL, VG.Proof.Poly1305.Arm.tw0, VG.Proof.Poly1305.Arm.tw1, VG.Proof.Poly1305.Arm.tw2, VG.Proof.Poly1305.Arm.tw3]; omega_using []

theorem epilogue_ok {s₀ : State} (hp : VG.Proof.Poly1305.Arm.BPre s₀) {s : State} (hc : VG.Proof.Poly1305.Arm.Common s₀ (VG.Proof.Poly1305.Arm.nb s₀) s) :
    WP isa (.block (reduce ++ toWords ++ ([.str .r3 .r0 0, .str .r5 .r0 4, .str .r7 .r0 8, .str .r10 .r0 12,
      .str .r1 .r0 16, .mov .r2 (.imm 0), .str .r2 .r0 20] : List Instr) ++ restoreRegs)) s fun s' =>
      abiPreserved s₀ s' ∧ Proof.Poly1305.blocksArm.post s₀ s' := by
  have hfit := hp.st_fit
  obtain ⟨D, hcD, hDb, hDv⟩ := hc.acc
  have hs0 : s.gpr .r0 = s₀.gpr .r0 := hc.keeps.gpr _ (by decide)
  have hw : VG.Proof.Poly1305.Arm.stR (s₀.gpr .r0) ∈ s.wr := by rw [hc.keeps.wr, hp.wr]; exact List.mem_singleton_self _
  have hE : ∀ j < 10, D j < 2 ^ 32 - 2 ^ 19 := fun j hj => by have := hDb j hj; omega_using [this]
  obtain ⟨-, -, -, hvL, hlL⟩ := VG.Proof.Poly1305.Arm.red_facts D hE
  simp only [List.append_assoc]
  refine WP.append (VG.Proof.Poly1305.Arm.reduce_ok hfit hDb hs0 hw hcD) fun s₁ ⟨hc₁, k₁⟩ => ?_
  refine WP.append (VG.Proof.Poly1305.Arm.toWords_ok hc₁ fun j hj => hlL j (by omega_using [hj])) fun s₂ ⟨e3, e5, e7, e10, e1, k₂⟩ => ?_
  have k₁₂ := k₁.trans (k₂.mono fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [VG.Proof.Poly1305.Arm.cregs, VG.Proof.Poly1305.Arm.yregs])
  have hs₂0 : s₂.gpr .r0 = s₀.gpr .r0 := by rw [k₁₂.gpr _ (by decide), hs0]
  have hw₂ : VG.Proof.Poly1305.Arm.stR (s₀.gpr .r0) ∈ s₂.wr := by rw [k₁₂.wr]; exact hw
  rw [VG.Proof.Poly1305.Arm.epi_eq]
  refine WP.append (VG.Proof.Poly1305.Arm.stores_ok .r0 hfit rfl VG.Proof.Poly1305.Arm.accList s₂ hs₂0 hw₂ (by decide) (by decide))
    fun s₃ ⟨hs₃, hf₃, hg₃, hrd₃, hwr₃, hsp₃⟩ => ?_
  refine VG.Proof.Poly1305.Arm.wp_mov (VG.Proof.Poly1305.Arm.op2_imm (by decide)) fun s₄ u₄ => ?_
  refine VG.Proof.Poly1305.Arm.wp_str (a := VG.Proof.Poly1305.Arm.stB s₀ + BitVec.ofNat 64 20) (by decide)
    (by rw [u₄.other _ (by decide), hg₃, hs₂0]; exact VG.Proof.Poly1305.Arm.ea hfit (off := 20) (by decide))
    (by rw [u₄.wr, hwr₃]; exact VG.Proof.Poly1305.Arm.outSt hw₂ (off := 20) (n := 4) (by decide)) fun s₅ u₅ => ?_
  have m₅ : s₅.mem = s₃.mem.writeW (VG.Proof.Poly1305.Arm.stB s₀ + BitVec.ofNat 64 20) (0 : BitVec 32) := by rw [u₅.mem, u₄.gpr, u₄.mem]
  have f₅ : Frame (VG.Proof.Poly1305.Arm.offR (VG.Proof.Poly1305.Arm.stB s₀) [(0, 24)]) s.mem s₅.mem := by
    rw [m₅, ← k₁₂.mem]
    rw [VG.Proof.Poly1305.Arm.accList_frame] at hf₃
    exact Frame.writeOff (hf₃.offR_sub (by decide) (by decide)) (a := 0) (len := 24) (by decide) (by decide)
      (by decide) (by decide) _ rfl
  have hs₅0 : s₅.gpr .r0 = s₀.gpr .r0 := by rw [u₅.gpr, u₄.other _ (by decide), hg₃, hs₂0]
  have hw₅ : VG.Proof.Poly1305.Arm.stR (s₀.gpr .r0) ∈ s₅.wr := by rw [u₅.wr, u₄.wr, hwr₃]; exact hw₂
  refine WP.mono (VG.Proof.Poly1305.Arm.restoreRegs_ok hfit hs₅0 hw₅ (hc.saved.frame f₅ (by decide) (by decide)))
    fun s' ⟨hr', k'⟩ => ?_
  have f' : Frame (VG.Proof.Poly1305.Arm.offR (VG.Proof.Poly1305.Arm.stB s₀) VG.Proof.Poly1305.Arm.wkL) s₀.mem s'.mem := by
    rw [k'.mem]; exact hc.keeps.frame.trans (f₅.offR_sub (by decide) (by decide))
  -- The words stored.
  have w : ∀ x ∈ VG.Proof.Poly1305.Arm.accList, ∀ d, x.2.1 = d → x.2.2 = false →
      s'.mem.readW (VG.Proof.Poly1305.Arm.stB s₀ + BitVec.ofNat 64 d) 32 = s₂.gpr x.1 := by
    intro x hx d hd hb
    have := hs₃ x hx
    obtain ⟨r, o, b⟩ := x
    simp only at hd hb; subst hd hb
    have hl : o + 4 ≤ 20 := by
      have : ∀ x ∈ VG.Proof.Poly1305.Arm.accList, x.2.1 + 4 ≤ 20 := by decide
      exact this _ hx
    rw [k'.mem, m₅, VG.Proof.Poly1305.Arm.readW_writeW_off _ _ _ (by omega_using [hl]) (by decide) (by omega_using [hl])]
    exact this
  refine ⟨⟨fun r hr => ?_, ?_⟩, fun key msg hrep => ?_⟩
  · rcases VG.Proof.Poly1305.Arm.preserved_cases r hr with rfl | ⟨i, hi, rfl⟩
    · rw [k'.gpr _ (by decide), u₅.gpr, u₄.other _ (by decide), hg₃, k₁₂.gpr _ (by decide),
        hc.keeps.gpr _ (by decide)]
    · exact hr' i hi
  · rw [k'.sp, u₅.sp, u₄.sp, hsp₃, k₁₂.sp, hc.keeps.sp]
  · obtain ⟨hlen, hkey, hacc⟩ := hrep
    have hkey' := hkey
    rw [← VG.Proof.Poly1305.Arm.key_frame f' (by decide) (by decide)] at hkey'
    refine ⟨?_, hkey', ?_⟩
    · rw [List.length_append, Poly1305.length_bytesAt]; omega_using [hlen]
    · have e0 := w _ (by decide : (Reg.r3, 0, false) ∈ accList) 0 rfl rfl
      have e4 := w _ (by decide : (Reg.r5, 4, false) ∈ accList) 4 rfl rfl
      have e8 := w _ (by decide : (Reg.r7, 8, false) ∈ accList) 8 rfl rfl
      have e12 := w _ (by decide : (Reg.r10, 12, false) ∈ accList) 12 rfl rfl
      have e16 := w _ (by decide : (Reg.r1, 16, false) ∈ accList) 16 rfl rfl
      have e20 : s'.mem.readW (VG.Proof.Poly1305.Arm.stB s₀ + BitVec.ofNat 64 20) 32 = 0 := by rw [k'.mem, m₅, Mem.readW_writeW_self32]
      simp only at e0 e4 e8 e12 e16
      rw [← hkey, VG.Proof.Poly1305.Arm.take_bytesAt _ _ (by decide), ← VG.Proof.Poly1305.Arm.val_rlimb, Poly1305.accumulate_append hlen]
      rw [← hkey, VG.Proof.Poly1305.Arm.take_bytesAt _ _ (by decide), ← VG.Proof.Poly1305.Arm.val_rlimb] at hacc
      have hlt : leNum (bytesAt s₀.mem (VG.Proof.Poly1305.Arm.stB s₀) 24) < P := by
        rw [hacc]; exact Poly1305.accumulate_lt _ _
      have hA : accumulate (VG.Proof.Poly1305.Arm.Rn s₀) msg = VG.Proof.Poly1305.Arm.A0 s₀ := by
        rw [VG.Proof.Poly1305.Arm.A0, VG.Proof.Poly1305.Arm.val_accD_eq hlt]; exact hacc.symm
      rw [hA, VG.Proof.Poly1305.Arm.leNum_bytesAt_24, e0, e4,
        e8, e12, e16, e20, e3, e5, e7, e10, e1]
      have hlt' := Poly1305.absorbAll_lt (r := VG.Proof.Poly1305.Arm.Rn s₀) (a := VG.Proof.Poly1305.Arm.A0 s₀) (by rw [← hA]; exact Poly1305.accumulate_lt _ _)
        (VG.Proof.Poly1305.Arm.blks s₀ (VG.Proof.Poly1305.Arm.nb s₀))
      rw [show (0 : BitVec 32).toNat = 0 from rfl, VG.Proof.Poly1305.Arm.val_words (fun j hj => hlL j (by omega_using [hj])), hvL, hDv,
        Nat.mod_eq_of_lt hlt']

/-! ## The whole function -/

theorem blocks_correct {s₀ : State} (hp : VG.Proof.Poly1305.Arm.BPre s₀) :
    WP isa blocks s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Poly1305.blocksArm.post s₀ s' := by
  refine WP.seq (WP.mono (VG.Proof.Poly1305.Arm.prologue_ok hp) fun s₁ ⟨hL, hz⟩ => ?_)
  refine WP.seq (WP.mono (Q := VG.Proof.Poly1305.Arm.Common s₀ (VG.Proof.Poly1305.Arm.nb s₀)) ?_ fun s₂ hc => VG.Proof.Poly1305.Arm.epilogue_ok hp hc)
  refine WP.ite s₁.z (VG.Proof.Poly1305.Arm.eval_eq _) (fun h => ?_) (fun h => ?_)
  · have h0 : VG.Proof.Poly1305.Arm.nb s₀ = 0 := by rw [h] at hz; simp only [VG.Proof.Poly1305.Arm.nb]; rw [eq_of_beq hz.symm]; rfl
    exact WP.block_nil (M := isa) (h0 ▸ hL.toCommon)
  · have hpos : 0 < VG.Proof.Poly1305.Arm.nb s₀ := by
      rw [h] at hz
      refine Nat.pos_of_ne_zero fun h' => ?_
      have : s₀.gpr .r2 = 0 := BitVec.eq_of_toNat_eq (by simpa [VG.Proof.Poly1305.Arm.nb] using h')
      simp [this] at hz
    refine WP.loop (M := isa) (fun m s => ∃ i, m = VG.Proof.Poly1305.Arm.nb s₀ - i ∧ i < VG.Proof.Poly1305.Arm.nb s₀ ∧ VG.Proof.Poly1305.Arm.LInv s₀ i s) ?_ (VG.Proof.Poly1305.Arm.nb s₀) s₁
      ⟨0, rfl, hpos, hL⟩
    rintro m s ⟨i, rfl, hi, hLi⟩
    refine WP.mono (VG.Proof.Poly1305.Arm.body_ok hp hi hLi) fun s' h' => ?_
    rcases h' with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
    · exact .inl ⟨he, hc⟩
    · exact .inr ⟨he, VG.Proof.Poly1305.Arm.nb s₀ - (i + 1), by omega_using [hi'], i + 1, rfl, hi', hL'⟩

/-! ## Constant time -/

/-- The initial taint of `blocks`: `r0`–`r2` are public, and `r0` points at
the state, whose public slots (the block pointer and count) the analysis
tracks. -/
def τb : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2], flags := false, lens := [128], bases := [(.r0, 0)] }

theorem wfb {s : State} (h : Proof.Poly1305.blocksArm.pre s) : VG.Arm.Taint.Wf VG.Proof.Poly1305.Arm.τb s := by
  have hp := BPre.of s h
  refine ⟨fun _ => ⟨by simp [hp.wr, VG.Proof.Poly1305.Arm.τb], by simp [hp.wr], ?_⟩, ?_, fun h => absurd h (by decide),
    fun _ h => (List.not_mem_nil h).elim⟩
  · simp only [hp.wr, List.mem_singleton, forall_eq]
    rw [VG.Proof.Poly1305.Arm.addr_toNat]; exact hp.st_fit
  · intro p hp'; simp only [VG.Proof.Poly1305.Arm.τb, List.mem_singleton] at hp'; subst hp'; simp [VG.Arm.Taint.region, hp.wr]

theorem agreeb {s₁ s₂ : State} (h₁ : Proof.Poly1305.blocksArm.pre s₁) (h₂ : Proof.Poly1305.blocksArm.pre s₂)
    (hpub : Proof.Poly1305.blocksArm.pub s₁ s₂) : VG.Arm.Taint.Agree VG.Proof.Poly1305.Arm.τb s₁ s₂ := by
  obtain ⟨p0, p1, p2⟩ := hpub
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, VG.Proof.Poly1305.Arm.wfb h₁, VG.Proof.Poly1305.Arm.wfb h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun h => absurd h (by decide),
    fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  · simp only [VG.Proof.Poly1305.Arm.τb, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> with_reducible assumption
  · rw [(BPre.of s₁ h₁).wr, (BPre.of s₂ h₂).wr, p0]

/-- A state satisfying the precondition (with no blocks). -/
def blocksSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 128⟩]

theorem blocks_ok (s : State) (hs : Proof.Poly1305.blocksArm.pre s) :
    ∃ t s', Exec isa Impl.Poly1305.Arm.blocks s t s' ∧ abiPreserved s s' ∧
      Proof.Poly1305.blocksArm.post s s' :=
  VG.Proof.Poly1305.Arm.blocks_correct (BPre.of s hs)

theorem blocks_ct : ConstantTime isa Proof.Poly1305.blocksArm.pre Proof.Poly1305.blocksArm.pub
    Impl.Poly1305.Arm.blocks := by
  exact VG.Taint.constantTime (A := taint) VG.Proof.Poly1305.Arm.τb (fun _ _ h₁ h₂ hp => VG.Proof.Poly1305.Arm.agreeb h₁ h₂ hp) (by
      taint_decide)

theorem blocks_verified :
    Verified Arm.target Impl.Poly1305.Arm.blocks (Spec.Poly1305.blocksContract Arm.abi) :=
  Verified.of_correct VG.Proof.Poly1305.Arm.blocks_ok VG.Proof.Poly1305.Arm.blocks_ct (by
    sig_implies [Spec.Poly1305.blocksContract, Spec.Poly1305.blocksSig, Proof.Poly1305.blocksArm,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [Proof.Poly1305.Arm.blocksSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using
      Proof.Poly1305.Arm.blocksSat)

end VG.Proof.Poly1305.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Poly1305.Arm.Init`. -/
section

/-!
# Poly1305 on 32-bit ARM: `init`

The key is copied to `[24, 56)` of the state, a word at a time, and the
accumulator's six words are zeroed.
-/

namespace VG.Proof.Poly1305.Arm

open VG VG.Arm VG.Impl.Poly1305.Arm
open VG.Spec.Poly1305 (P clamp leNum bytesAt accumulate Repr)

/-- The precondition of `init`, by field. -/
structure IPre (s₀ : State) : Prop where
  rd : s₀.rd = [⟨State.addr (s₀.gpr .r1), 32⟩]
  wr : s₀.wr = [VG.Proof.Poly1305.Arm.stR (s₀.gpr .r0)]
  st_key : (VG.Proof.Poly1305.Arm.stR (s₀.gpr .r0)).Disjoint ⟨State.addr (s₀.gpr .r1), 32⟩
  st_fit : (s₀.gpr .r0).toNat + 128 ≤ 2 ^ 32
  key_fit : (s₀.gpr .r1).toNat + 32 ≤ 2 ^ 32

/-- After copying `i` words of the key. -/
structure KI (s₀ : State) (i : Nat) (s : State) : Prop where
  words : ∀ j < i, s.mem.readW (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 (24 + 4 * j)) 32 =
    s₀.mem.readW (State.addr (s₀.gpr .r1) + BitVec.ofNat 64 (4 * j)) 32
  keeps : VG.Proof.Poly1305.Arm.KeepsF [.r2] [VG.Proof.Poly1305.Arm.stR (s₀.gpr .r0)] s₀ s

theorem key_step {s₀ : State} (hp : VG.Proof.Poly1305.Arm.IPre s₀) (i : Nat) (s : State) (hi : i < 8) (h : VG.Proof.Poly1305.Arm.KI s₀ i s) :
    WP isa (.block [.ldr .r2 .r1 (4 * i), .str .r2 .r0 (24 + 4 * i)]) s (VG.Proof.Poly1305.Arm.KI s₀ (i + 1)) := by
  have hkd : ∀ r' ∈ [VG.Proof.Poly1305.Arm.stR (s₀.gpr .r0)],
      (⟨State.addr (s₀.gpr .r1) + BitVec.ofNat 64 (4 * i), 4⟩ : Region).Disjoint r' := by
    simp only [List.mem_singleton, forall_eq]
    exact (hp.st_key.sub_right (VG.Proof.Poly1305.Arm.sub_base _ (by omega) (by decide))).symm
  have h1 : s.gpr .r1 = s₀.gpr .r1 := h.keeps.gpr _ (by decide)
  have h0 : s.gpr .r0 = s₀.gpr .r0 := h.keeps.gpr _ (by decide)
  refine VG.Proof.Poly1305.Arm.wp_ldr (a := State.addr (s₀.gpr .r1) + BitVec.ofNat 64 (4 * i)) (by omega)
    (by rw [h1]; exact addr_add (by have := hp.key_fit; omega))
    (by rw [h.keeps.rd, hp.rd]; exact ⟨_, List.mem_append_left _ (List.mem_singleton_self _),
      VG.Proof.Poly1305.Arm.contains_base _ (by omega) (by decide)⟩) fun s1 u1 => ?_
  refine VG.Proof.Poly1305.Arm.wp_str (a := State.addr (s₀.gpr .r0) + BitVec.ofNat 64 (24 + 4 * i)) (by omega)
    (by rw [u1.other _ (by decide), h0]; exact VG.Proof.Poly1305.Arm.ea hp.st_fit (by omega))
    (by rw [u1.wr, h.keeps.wr]; exact VG.Proof.Poly1305.Arm.outSt (by rw [hp.wr]; exact List.mem_singleton_self _) (by omega))
    fun s2 u2 => WP.block_nil ⟨fun j hj => ?_, ?_⟩
  · rw [u2.mem]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h' | rfl
    · rw [VG.Proof.Poly1305.Arm.readW_writeW_off _ _ _ (by omega) (by omega) (by omega), u1.mem]; exact h.words j h'
    · rw [Mem.readW_writeW_self32, u1.gpr, h.keeps.frame.readW (Region.contains_self _ _) hkd (by decide)]
  · refine h.keeps.trans ⟨fun r hr => ?_, ?_, u2.rd.trans u1.rd, u2.wr.trans u1.wr, u2.sp.trans u1.sp⟩
    · rw [u2.gpr, u1.other _ (by simpa using hr)]
    · rw [u2.mem, u1.mem]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (VG.Proof.Poly1305.Arm.contains_off (by omega) (by omega))

/-- After zeroing `i` words of the accumulator. -/
structure ZI (s₀ : State) (i : Nat) (s : State) : Prop where
  zero : ∀ j < i, s.mem.readW (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 (4 * j)) 32 = 0
  key : ∀ j < 8, s.mem.readW (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 (24 + 4 * j)) 32 =
    s₀.mem.readW (State.addr (s₀.gpr .r1) + BitVec.ofNat 64 (4 * j)) 32
  r2 : s.gpr .r2 = 0
  keeps : VG.Proof.Poly1305.Arm.KeepsF [.r2] [VG.Proof.Poly1305.Arm.stR (s₀.gpr .r0)] s₀ s

theorem zero_step {s₀ : State} (hp : VG.Proof.Poly1305.Arm.IPre s₀) (i : Nat) (s : State) (hi : i < 6) (h : VG.Proof.Poly1305.Arm.ZI s₀ i s) :
    WP isa (.block [.str .r2 .r0 (4 * i)]) s (VG.Proof.Poly1305.Arm.ZI s₀ (i + 1)) := by
  have h0 : s.gpr .r0 = s₀.gpr .r0 := h.keeps.gpr _ (by decide)
  refine VG.Proof.Poly1305.Arm.wp_str (a := State.addr (s₀.gpr .r0) + BitVec.ofNat 64 (4 * i)) (by omega)
    (by rw [h0]; exact VG.Proof.Poly1305.Arm.ea hp.st_fit (by omega))
    (by rw [h.keeps.wr]; exact VG.Proof.Poly1305.Arm.outSt (by rw [hp.wr]; exact List.mem_singleton_self _) (by omega))
    fun s2 u2 => WP.block_nil ⟨fun j hj => ?_, fun j hj => ?_, by rw [u2.gpr, h.r2], ?_⟩
  · rw [u2.mem]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h' | rfl
    · rw [VG.Proof.Poly1305.Arm.readW_writeW_off _ _ _ (by omega) (by omega) (by omega)]; exact h.zero j h'
    · rw [Mem.readW_writeW_self32, h.r2]
  · rw [u2.mem, VG.Proof.Poly1305.Arm.readW_writeW_off _ _ _ (by omega) (by omega) (by omega)]; exact h.key j hj
  · refine h.keeps.trans ⟨fun r _ => by rw [u2.gpr], ?_, u2.rd, u2.wr, u2.sp⟩
    rw [u2.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (VG.Proof.Poly1305.Arm.contains_off (by omega) (by omega))

theorem accumulate_nil (r : Nat) : accumulate r [] = 0 := rfl

theorem init_correct {s₀ : State} (hp : VG.Proof.Poly1305.Arm.IPre s₀) :
    WP isa init s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Poly1305.initArm.post s₀ s' := by
  unfold init
  rw [← List.append_nil ((List.range 6).flatMap _)]
  refine WP.append (wp_range_flatMap (M := isa) (VG.Proof.Poly1305.Arm.KI s₀) (VG.Proof.Poly1305.Arm.key_step hp) 8 (Nat.le_refl _) s₀
    ⟨fun _ h => absurd h (by omega), (Keeps.refl _ _).keepsF _⟩) fun s₁ h₁ => ?_
  refine VG.Proof.Poly1305.Arm.wp_mov (VG.Proof.Poly1305.Arm.op2_imm (by decide)) fun s₂ u₂ => ?_
  refine WP.mono (wp_range_flatMap (M := isa) (VG.Proof.Poly1305.Arm.ZI s₀) (VG.Proof.Poly1305.Arm.zero_step hp) 6 (Nat.le_refl _) s₂
    ⟨fun _ h => absurd h (by omega), fun j hj => by rw [u₂.mem]; exact h₁.words j hj, u₂.gpr,
      h₁.keeps.trans ⟨fun r hr => u₂.other r (by simpa using hr), by rw [u₂.mem]; exact Frame.refl _ _,
        u₂.rd, u₂.wr, u₂.sp⟩⟩) fun s' h' => ⟨⟨fun r hr => ?_, h'.keeps.sp⟩, ?_, ?_, ?_⟩
  · exact h'.keeps.gpr r fun e => by simp only [List.mem_singleton] at e; subst e; simp [preserved] at hr
  · rfl
  · show bytesAt s'.mem (State.addr (s₀.gpr .r0) + 24) 32 = bytesAt s₀.mem (State.addr (s₀.gpr .r1)) 32
    rw [show (32 : Nat) = 4 * 8 from rfl]
    refine VG.Proof.Poly1305.Arm.bytesAt_eq_of_words fun j hj => ?_
    rw [show (24 : Addr) = BitVec.ofNat 64 24 from rfl, VG.Proof.Poly1305.Arm.off_add]
    exact h'.key j hj
  · show leNum (bytesAt s'.mem (State.addr (s₀.gpr .r0)) 24) = accumulate _ []
    rw [VG.Proof.Poly1305.Arm.accumulate_nil, VG.Proof.Poly1305.Arm.leNum_bytesAt_24, h'.zero 0 (by decide), h'.zero 1 (by decide),
      h'.zero 2 (by decide), h'.zero 3 (by decide), h'.zero 4 (by decide), h'.zero 5 (by decide)]
    rfl

theorem IPre.of (s : State) (h : Proof.Poly1305.initArm.pre s) : VG.Proof.Poly1305.Arm.IPre s := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

/-- A state satisfying the precondition. -/
def initSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x2000, 32⟩]
  wr := [⟨0x1000, 128⟩]

theorem init_ok (s : State) (hs : Proof.Poly1305.initArm.pre s) :
    ∃ t s', Exec isa Impl.Poly1305.Arm.init s t s' ∧ abiPreserved s s' ∧
      Proof.Poly1305.initArm.post s s' := by
  exact VG.Proof.Poly1305.Arm.init_correct (IPre.of s hs)

theorem init_ct : ConstantTime isa Proof.Poly1305.initArm.pre Proof.Poly1305.initArm.pub
    Impl.Poly1305.Arm.init := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> with_reducible assumption

theorem init_verified :
    Verified Arm.target Impl.Poly1305.Arm.init (Spec.Poly1305.initContract Arm.abi) :=
  Verified.of_correct VG.Proof.Poly1305.Arm.init_ok VG.Proof.Poly1305.Arm.init_ct (by
    sig_implies [Spec.Poly1305.initContract, Spec.Poly1305.initSig, Proof.Poly1305.initArm, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [Proof.Poly1305.Arm.initSat,
      Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using Proof.Poly1305.Arm.initSat)

end VG.Proof.Poly1305.Arm

end
