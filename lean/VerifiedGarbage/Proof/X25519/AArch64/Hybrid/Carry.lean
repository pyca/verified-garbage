module

public import VerifiedGarbage.Proof.X25519.AArch64.Hybrid.Radix
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# Radix 2²⁵·⁵: carries

Untrusted: everything here is checked by Lean. A carry keeps the value of the
limbs modulo `p` (`val_carryStep`); bounds on the limbs before the carries of
`Neon.prod2` bound them after (`carries_le`).
-/

@[expose] public section

namespace VG.Proof.X25519.AArch64.Hybrid

open VG.Spec.X25519 (P)
open VG.Impl.X25519.AArch64.Neon (limbOff width)

/-! ## Carries -/

/-- What a carry out of coefficient `i` adds to the next: the carry, 19 times for `i = 9`. -/
def carryMul (i : Nat) : Nat := if i = 9 then 19 else 1

/-- Carry coefficient `i` into `i + 1` (19 times into 0 for `i = 9`). -/
def carryStep (i : Nat) (h : Nat → Nat) (k : Nat) : Nat :=
  if k = i then h i % 2 ^ width i
  else if k = (i + 1) % 10 then h k + carryMul i * (h i / 2 ^ width i) else h k

theorem val_carryStep_lt (h : Nat → Nat) : ∀ i < 9, val (carryStep i h) = val h := by
  intro i hi
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · simp only [val, S10, carryStep, carryMul, width, limbOff, List.getD_cons_succ, List.getD_cons_zero,
      Nat.reduceAdd, Nat.reduceMod]
    simp only [reduceIte, Nat.reduceEqDiff]
    first
      | (have := Nat.mod_add_div (h 0) (2 ^ 26); omega)
      | (have := Nat.mod_add_div (h 1) (2 ^ 25); omega)
      | (have := Nat.mod_add_div (h 2) (2 ^ 26); omega)
      | (have := Nat.mod_add_div (h 3) (2 ^ 25); omega)
      | (have := Nat.mod_add_div (h 4) (2 ^ 26); omega)
      | (have := Nat.mod_add_div (h 5) (2 ^ 25); omega)
      | (have := Nat.mod_add_div (h 6) (2 ^ 26); omega)
      | (have := Nat.mod_add_div (h 7) (2 ^ 25); omega)
      | (have := Nat.mod_add_div (h 8) (2 ^ 26); omega)

theorem val_carryStep_9 (h : Nat → Nat) : val h = val (carryStep 9 h) + h 9 / 2 ^ 25 * P := by
  simp only [val, S10, carryStep, carryMul, width, limbOff, List.getD_cons_succ, List.getD_cons_zero,
    Nat.reduceAdd, Nat.reduceMod, P]
  simp only [reduceIte, Nat.reduceEqDiff]
  have := Nat.mod_add_div (h 9) (2 ^ 25)
  omega

theorem val_carryStep (h : Nat → Nat) {i : Nat} (hi : i < 10) : val (carryStep i h) % P = val h % P := by
  rcases Nat.lt_or_ge i 9 with h9 | h9
  · rw [val_carryStep_lt h i h9]
  · rw [show i = 9 by omega, val_carryStep_9 h, Nat.add_mul_mod_self_right]

/-- The carries of `Neon.prod2`, in order. -/
def carries (h : Nat → Nat) : Nat → Nat :=
  VG.Impl.X25519.AArch64.Neon.carryOrder.foldl (fun h i => carryStep i h) h

theorem val_carries_go (h : Nat → Nat) : ∀ (l : List Nat), (∀ i ∈ l, i < 10) →
    val (l.foldl (fun h i => carryStep i h) h) % P = val h % P
  | [], _ => rfl
  | i :: l, hl => by
    rw [List.foldl_cons, val_carries_go _ l fun j hj => hl j (List.mem_cons_of_mem _ hj),
      val_carryStep h (hl i List.mem_cons_self)]

theorem val_carries (h : Nat → Nat) : val (carries h) % P = val h % P :=
  val_carries_go h _ (by decide)

/-! ## Bounds -/

/-- A bound after a carry, from bounds before it. -/
def carryB (i : Nat) (B : Nat → Nat) (k : Nat) : Nat :=
  if k = i then 2 ^ width i - 1
  else if k = (i + 1) % 10 then B k + carryMul i * (B i / 2 ^ width i) else B k

theorem carryStep_le {h B : Nat → Nat} (hb : ∀ k < 10, h k ≤ B k) {i : Nat} (hi : i < 10) :
    ∀ k < 10, carryStep i h k ≤ carryB i B k := by
  intro k hk
  simp only [carryStep, carryB]
  split
  · have := Nat.mod_lt (h i) (Nat.two_pow_pos (width i)); omega
  · split
    · exact Nat.add_le_add (hb k hk) (Nat.mul_le_mul_left _ (Nat.div_le_div_right (hb i hi)))
    · exact hb k hk

/-- No carry overflows a 64-bit lane: the sum, and 16 and 19 times the carry out of 9. -/
def carryFits (i : Nat) (B : Nat → Nat) : Bool :=
  decide (carryB i B ((i + 1) % 10) < 2 ^ 64) && decide (19 * (B i / 2 ^ width i) < 2 ^ 64)

/-- The bounds after carries, and whether each fits. -/
def carriesB (B : Nat → Nat) : List Nat → (Nat → Nat) × Bool
  | [] => (B, true)
  | i :: l => let r := carriesB (carryB i B) l; (r.1, carryFits i B && r.2)

/-- The largest limbs of a number below 2²⁵⁶. -/
def maxLimb (i : Nat) : Nat := 2 ^ wdIn i - 1

/-- Bounds on the coefficients of the product of limbs of numbers below 2²⁵⁶. -/
def prodB (k : Nat) : Nat := prodCoef maxLimb maxLimb k

theorem S10_le {a b : Nat → Nat} (h : ∀ i < 10, a i ≤ b i) : S10 a ≤ S10 b := by
  simp only [S10]
  have := h 0 (by decide); have := h 1 (by decide); have := h 2 (by decide); have := h 3 (by decide)
  have := h 4 (by decide); have := h 5 (by decide); have := h 6 (by decide); have := h 7 (by decide)
  have := h 8 (by decide); have := h 9 (by decide)
  omega

theorem colOf_lt (i k : Nat) : colOf i k < 10 := Nat.mod_lt _ (by decide)

theorem prodCoef_le {f g : Nat → Nat} (hf : ∀ i < 10, f i ≤ maxLimb i) (hg : ∀ i < 10, g i ≤ maxLimb i) (k : Nat) :
    prodCoef f g k ≤ prodB k := by
  unfold prodB prodCoef
  refine S10_le fun i hi => ?_
  exact Nat.mul_le_mul (Nat.mul_le_mul_left (coef i (colOf i k)) (hf i hi)) (hg _ (colOf_lt i k))

/-- The bounds after `Neon.prod2`'s carries: every limb below 2²⁷, and no lane overflows on the way. -/
theorem carriesB_prodB :
    (carriesB prodB VG.Impl.X25519.AArch64.Neon.carryOrder).2 = true ∧
    ∀ k < 10, (carriesB prodB VG.Impl.X25519.AArch64.Neon.carryOrder).1 k < 2 ^ 27 := by
  decide +kernel

theorem carries_le_go : ∀ (l : List Nat) (h : Nat → Nat) (B : Nat → Nat), (∀ i ∈ l, i < 10) →
    (∀ k < 10, h k ≤ B k) → ∀ k < 10, l.foldl (fun h i => carryStep i h) h k ≤ (carriesB B l).1 k
  | [], _, _, _, hb => hb
  | i :: l, _, _, hl, hb => carries_le_go l _ _ (fun j hj => hl j (List.mem_cons_of_mem _ hj))
      (carryStep_le hb (hl i List.mem_cons_self))

/-- The limbs after `Neon.prod2`'s carries are below 2²⁷. -/
theorem carries_prod_lt {f g : Nat → Nat} (hf : ∀ i < 10, f i ≤ maxLimb i) (hg : ∀ i < 10, g i ≤ maxLimb i) :
    ∀ k < 10, carries (prodCoef f g) k < 2 ^ 27 := fun k hk =>
  Nat.lt_of_le_of_lt (carries_le_go _ _ _ (by decide) (fun k _ => prodCoef_le hf hg k) k hk) (carriesB_prodB.2 k hk)

end VG.Proof.X25519.AArch64.Hybrid
