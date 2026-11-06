module

public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Spec.X448
import Batteries.Tactic.Init
import Std.Data.DTreeMap.Internal.Operations

/-!
# X448: radix-2²⁸ arithmetic

The sixteen limbs of a field element, carries, and reduction using `2^448 =
2^224 + 1` modulo p. These lemmas do not depend on an instruction set.
-/

@[expose] public section

namespace VG.Proof.X448

open VG.Spec.X448

def radix : Nat := 2 ^ 28
def full : Nat := radix ^ 16
def half : Nat := radix ^ 8

theorem full_eq : full = P + (half + 1) := by decide +kernel
/-- Read `n` limbs, lowest first. -/
def valN (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => valN f n + radix ^ n * f n

theorem valN_succ (f : Nat → Nat) (n : Nat) :
    valN f (n + 1) = valN f n + radix ^ n * f n := rfl

theorem valN_congr {f g : Nat → Nat} {n : Nat}
    (h : ∀ i < n, f i = g i) : valN f n = valN g n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [valN, valN, ih (fun i hi => h i (by omega)), h n (by omega)]

theorem valN_add (f g : Nat → Nat) (n : Nat) :
    valN (fun i => f i + g i) n = valN f n + valN g n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [valN, valN, valN, ih, Nat.mul_add]; omega

theorem valN_split (f : Nat → Nat) (a b : Nat) :
    valN f (a + b) = valN f a + radix ^ a * valN (fun i => f (a + i)) b := by
  induction b with
  | zero => simp only [Nat.add_zero, valN, Nat.mul_zero]
  | succ b ih => rw [Nat.add_succ, valN, valN, ih, Nat.pow_add, Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

theorem valN_lt {f : Nat → Nat} {n : Nat} (h : ∀ i < n, f i < radix) :
    valN f n < radix ^ n := by
  induction n with
  | zero => simp only [valN, Nat.pow_zero]; decide
  | succ n ih =>
    have hn := h n (by omega)
    have hp := ih fun i hi => h i (by omega)
    have hm := Nat.mul_le_mul_left (radix ^ n) hn
    rw [Nat.mul_succ] at hm
    rw [valN, Nat.pow_succ]
    omega

/-- The incoming carry at position `n`. -/
def carry (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => (f n + carry f n) / radix

def digit (f : Nat → Nat) (i : Nat) : Nat := (f i + carry f i) % radix

theorem digit_lt (f : Nat → Nat) (i : Nat) : digit f i < radix :=
  Nat.mod_lt _ (by decide)

theorem pass_eq (f : Nat → Nat) (n : Nat) :
    valN (digit f) n + radix ^ n * carry f n = valN f n := by
  induction n with
  | zero => simp only [valN, carry, Nat.mul_zero, Nat.add_zero]
  | succ n ih =>
    have hd := Nat.mod_add_div (f n + carry f n) radix
    change digit f n + radix * carry f (n + 1) = f n + carry f n at hd
    rw [valN, valN, Nat.pow_succ, Nat.mul_assoc, Nat.add_assoc, ← Nat.mul_add, hd,
      Nat.mul_add]
    omega

theorem carry_bound {f : Nat → Nat} {n : Nat} (h : ∀ i < n, f i < 2 ^ 62) :
    carry f n < 2 ^ 35 := by
  induction n with
  | zero => simp only [carry]; decide
  | succ n ih =>
    have hi := ih fun i hi => h i (by omega)
    have hn := h n (by omega)
    simp only [carry, radix]
    omega

end VG.Proof.X448
