module

public import VerifiedGarbage.Impl.X25519.AArch64.Neon
public import VerifiedGarbage.Proof.X25519.Field
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# Radix 2²⁵·⁵: limbs, products and carries as numbers

Untrusted: everything here is checked by Lean. A number below 2²⁵⁶ is the
value of its ten radix-2²⁵·⁵ limbs (`val_limbOf`). The coefficients `prodCoef`
of `Neon.prod2` (limb `i` of `f` times limb `j` of `g` at coefficient
`i + j mod 10`, doubled if both are odd and times 19 if they wrap) add up to
the product modulo `p` (`val_prodCoef`), and a carry keeps the value modulo
`p` (`val_carryStep`).
-/

@[expose] public section

namespace VG.Proof.X25519.AArch64.Hybrid

open VG.Spec.X25519 (P)
open VG.Impl.X25519.AArch64.Neon (limbOff width)

/-- Ten terms. -/
def S10 (φ : Nat → Nat) : Nat := φ 0 + φ 1 + φ 2 + φ 3 + φ 4 + φ 5 + φ 6 + φ 7 + φ 8 + φ 9

/-- The value of ten radix-2²⁵·⁵ limbs. -/
def val (h : Nat → Nat) : Nat := S10 fun i => h i * 2 ^ limbOff i

/-- The width of limb `i` split from a number below 2²⁵⁶: limb 9 takes the bits up to 2²⁵⁶. -/
def wdIn (i : Nat) : Nat := if i = 9 then 26 else width i

/-- Limb `i` of `x`. -/
def limbOf (x i : Nat) : Nat := x / 2 ^ limbOff i % 2 ^ wdIn i

/-- The first `n` limbs' terms. -/
def valN (h : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => valN h n + h n * 2 ^ limbOff n

/-- Where limb `n` starts (256 for `n = 10`). -/
def start (n : Nat) : Nat := if n < 10 then limbOff n else 256

theorem start_succ : ∀ n < 10, start (n + 1) = start n + wdIn n := by decide

theorem start_eq : ∀ n < 10, start n = limbOff n := by decide

theorem valN_limbOf (x : Nat) : ∀ n ≤ 10, valN (limbOf x) n = x % 2 ^ start n
  | 0, _ => by simp [valN, start, limbOff, Nat.mod_one]
  | n + 1, hn => by
    rw [valN, valN_limbOf x n (by omega), start_succ n (by omega), Nat.pow_add, Nat.mod_mul, limbOf,
      ← start_eq n (by omega), Nat.mul_comm]

theorem val_eq_valN (h : Nat → Nat) : val h = valN h 10 := by
  simp only [val, S10, valN, Nat.zero_add]

/-- A number below 2²⁵⁶ is the value of its limbs. -/
theorem val_limbOf {x : Nat} (hx : x < 2 ^ 256) : val (limbOf x) = x := by
  rw [val_eq_valN, valN_limbOf x 10 (by omega), show start 10 = 256 from rfl, Nat.mod_eq_of_lt hx]

theorem limbOf_lt (x i : Nat) : limbOf x i < 2 ^ wdIn i := Nat.mod_lt _ (Nat.two_pow_pos _)

theorem wdIn_le (i : Nat) : wdIn i ≤ 26 := by
  simp only [wdIn, width]; split <;> (try split) <;> omega

theorem limbOf_lt26 (x i : Nat) : limbOf x i < 2 ^ 26 :=
  Nat.lt_of_lt_of_le (limbOf_lt x i) (Nat.pow_le_pow_right (by decide) (wdIn_le i))

/-! ## Products -/

/-- The coefficient of limb `i` of `f` times limb `j` of `g`, at coefficient `i + j mod 10`. -/
def coef (i j : Nat) : Nat := (if i % 2 = 1 ∧ j % 2 = 1 then 2 else 1) * (if 10 ≤ i + j then 19 else 1)

theorem coef_mod : ∀ i < 10, ∀ j < 10,
    2 ^ limbOff i * 2 ^ limbOff j % P = coef i j * 2 ^ limbOff ((i + j) % 10) % P := by decide

/-- The column of row `i` that coefficient `k` takes. -/
def colOf (i k : Nat) : Nat := (k + 10 - i) % 10

/-- Coefficient `k` of the product of the limbs `f` and `g`. -/
def prodCoef (f g : Nat → Nat) (k : Nat) : Nat := S10 fun i => coef i (colOf i k) * f i * g (colOf i k)

theorem S10_swap (a : Nat → Nat → Nat) : S10 (fun k => S10 fun i => a i k) = S10 (fun i => S10 fun k => a i k) := by
  simp only [S10]; omega

theorem S10_mul (φ : Nat → Nat) (c : Nat) : S10 φ * c = S10 fun i => φ i * c := by
  simp only [S10, Nat.add_mul]

theorem S10_rotate (φ : Nat → Nat) : ∀ i < 10, S10 φ = S10 fun j => φ ((i + j) % 10) := by
  intro i hi
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [S10, Nat.reduceAdd, Nat.reduceMod] <;> omega

theorem S10_congr_mod {a b : Nat → Nat} (h : ∀ i < 10, a i % P = b i % P) : S10 a % P = S10 b % P := by
  simp only [S10]
  simp only [Nat.add_mod (_ + _) (a 9), Nat.add_mod (_ + _) (b 9), Nat.add_mod (_ + _) (a 8), Nat.add_mod (_ + _) (b 8),
    Nat.add_mod (_ + _) (a 7), Nat.add_mod (_ + _) (b 7), Nat.add_mod (_ + _) (a 6), Nat.add_mod (_ + _) (b 6),
    Nat.add_mod (_ + _) (a 5), Nat.add_mod (_ + _) (b 5), Nat.add_mod (_ + _) (a 4), Nat.add_mod (_ + _) (b 4),
    Nat.add_mod (_ + _) (a 3), Nat.add_mod (_ + _) (b 3), Nat.add_mod (_ + _) (a 2), Nat.add_mod (_ + _) (b 2),
    Nat.add_mod (a 0) (a 1), Nat.add_mod (b 0) (b 1),
    h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide),
    h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide)]

theorem colOf_rot {i j : Nat} (hi : i < 10) (hj : j < 10) : colOf i ((i + j) % 10) = j := by
  simp only [colOf]; omega

theorem S10_congr {a b : Nat → Nat} (h : ∀ i < 10, a i = b i) : S10 a = S10 b := by
  simp only [S10, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide),
    h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide)]

theorem mul_S10 (c : Nat) (φ : Nat → Nat) : c * S10 φ = S10 fun i => c * φ i := by
  simp only [S10, Nat.mul_add]

/-- The coefficients of the product add up to the product, modulo `p`. -/
theorem val_prodCoef (f g : Nat → Nat) : val (prodCoef f g) % P = val f * val g % P := by
  have h1 : val (prodCoef f g) = S10 fun i => S10 fun j => coef i j * f i * g j * 2 ^ limbOff ((i + j) % 10) := by
    rw [val]
    simp only [prodCoef, S10_mul]
    rw [S10_swap]
    refine S10_congr fun i hi => ?_
    rw [S10_rotate _ i hi]
    exact S10_congr fun j hj => by rw [colOf_rot hi hj]
  have h2 : val f * val g = S10 fun i => S10 fun j => f i * g j * (2 ^ limbOff i * 2 ^ limbOff j) := by
    rw [val, S10_mul]
    refine S10_congr fun i _ => ?_
    rw [val, mul_S10]
    refine S10_congr fun j _ => ?_
    simp only [Nat.mul_assoc, Nat.mul_left_comm (2 ^ limbOff i)]
  rw [h1, h2]
  refine S10_congr_mod fun i hi => S10_congr_mod fun j hj => ?_
  rw [show coef i j * f i * g j * 2 ^ limbOff ((i + j) % 10) = f i * g j * (coef i j * 2 ^ limbOff ((i + j) % 10)) by
      simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc],
    Nat.mul_mod, ← coef_mod i hi j hj, ← Nat.mul_mod]

end VG.Proof.X25519.AArch64.Hybrid
