import VerifiedGarbage.Impl.X448.AArch64.Symmetric
import VerifiedGarbage.Impl.X448.AArch64.Cached
import VerifiedGarbage.Impl.X448.AArch64.Wide
import VerifiedGarbage.Proof.Ed25519.AArch64.MulAddVerified
import VerifiedGarbage.Proof.X448.Encoding
import Batteries.Tactic.Init
import VerifiedGarbage.Proof.Framework.PowLit
import Batteries.Logic
import VerifiedGarbage.Proof.X448.AArch64.PointwiseSmall
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Impl.X448.AArch64.Tail

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Wide.Limbs`. -/
section

/-!
# X448: radix-2⁵⁶ arithmetic

Untrusted: everything here is checked by Lean. The eight limbs of a
field element, carries, and reduction using `2^448 = 2^224 + 1` modulo p.
These lemmas do not depend on an instruction set.
-/

namespace VG.Proof.X448.Wide

open VG.Spec.X448 VG.Proof.X448

def radix : Nat := 2 ^ 56
def full : Nat := VG.Proof.X448.Wide.radix ^ 8
def half : Nat := VG.Proof.X448.Wide.radix ^ 4

theorem full_eq : VG.Proof.X448.Wide.full = VG.Spec.X448.P + (VG.Proof.X448.Wide.half + 1) := by decide +kernel
theorem half_sq : VG.Proof.X448.Wide.half * VG.Proof.X448.Wide.half = VG.Proof.X448.Wide.full := by decide +kernel

/-- Read `n` limbs, lowest first. -/
def valN (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => VG.Proof.X448.Wide.valN f n + VG.Proof.X448.Wide.radix ^ n * f n

theorem valN_succ (f : Nat → Nat) (n : Nat) :
    VG.Proof.X448.Wide.valN f (n + 1) = VG.Proof.X448.Wide.valN f n + VG.Proof.X448.Wide.radix ^ n * f n := rfl

theorem valN_congr {f g : Nat → Nat} {n : Nat}
    (h : ∀ i < n, f i = g i) : VG.Proof.X448.Wide.valN f n = VG.Proof.X448.Wide.valN g n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [VG.Proof.X448.Wide.valN, VG.Proof.X448.Wide.valN, ih (fun i hi => h i (by omega)), h n (by omega)]

theorem valN_add (f g : Nat → Nat) (n : Nat) :
    VG.Proof.X448.Wide.valN (fun i => f i + g i) n = VG.Proof.X448.Wide.valN f n + VG.Proof.X448.Wide.valN g n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [VG.Proof.X448.Wide.valN, VG.Proof.X448.Wide.valN, VG.Proof.X448.Wide.valN, ih, Nat.mul_add]; omega

theorem valN_scale (c : Nat) (f : Nat → Nat) (n : Nat) :
    VG.Proof.X448.Wide.valN (fun i => c * f i) n = c * VG.Proof.X448.Wide.valN f n := by
  induction n with
  | zero => simp only [VG.Proof.X448.Wide.valN, Nat.mul_zero]
  | succ n ih => rw [VG.Proof.X448.Wide.valN, VG.Proof.X448.Wide.valN, ih, Nat.mul_add, Nat.mul_left_comm (VG.Proof.X448.Wide.radix ^ n) c]

theorem valN_split (f : Nat → Nat) (a b : Nat) :
    VG.Proof.X448.Wide.valN f (a + b) = VG.Proof.X448.Wide.valN f a + VG.Proof.X448.Wide.radix ^ a * VG.Proof.X448.Wide.valN (fun i => f (a + i)) b := by
  induction b with
  | zero => simp only [Nat.add_zero, VG.Proof.X448.Wide.valN, Nat.mul_zero]
  | succ b ih => rw [Nat.add_succ, VG.Proof.X448.Wide.valN, VG.Proof.X448.Wide.valN, ih, Nat.pow_add, Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

theorem valN_lt {f : Nat → Nat} {n : Nat} (h : ∀ i < n, f i < VG.Proof.X448.Wide.radix) :
    VG.Proof.X448.Wide.valN f n < VG.Proof.X448.Wide.radix ^ n := by
  induction n with
  | zero => simp only [VG.Proof.X448.Wide.valN, Nat.pow_zero]; decide
  | succ n ih =>
    have hn := h n (by omega)
    have hp := ih fun i hi => h i (by omega)
    have hm := Nat.mul_le_mul_left (VG.Proof.X448.Wide.radix ^ n) hn
    rw [Nat.mul_succ] at hm
    rw [VG.Proof.X448.Wide.valN, Nat.pow_succ]
    omega

/-- Changing one limb changes the value at that limb's weight. -/
theorem valN_update {f g : Nat → Nat} {n k v : Nat} (hk : k < n)
    (h : ∀ i < n, g i = if i = k then f i + v else f i) :
    VG.Proof.X448.Wide.valN g n = VG.Proof.X448.Wide.valN f n + VG.Proof.X448.Wide.radix ^ k * v := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn : k = n
    · subst k
      have he : VG.Proof.X448.Wide.valN g n = VG.Proof.X448.Wide.valN f n := VG.Proof.X448.Wide.valN_congr fun i hi => by
        rw [h i (by omega), ite_eq_right (by omega)]
      rw [VG.Proof.X448.Wide.valN, VG.Proof.X448.Wide.valN, he, h n (by omega), ite_eq_left rfl, Nat.mul_add]
      omega
    · rw [VG.Proof.X448.Wide.valN, VG.Proof.X448.Wide.valN, ih (by omega) (fun i hi => h i (by omega)),
        h n (by omega), ite_eq_right (Ne.symm hn)]
      omega

/-- The incoming carry at position `n`. -/
def carry (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => (f n + VG.Proof.X448.Wide.carry f n) / VG.Proof.X448.Wide.radix

def digit (f : Nat → Nat) (i : Nat) : Nat := (f i + VG.Proof.X448.Wide.carry f i) % VG.Proof.X448.Wide.radix

theorem digit_lt (f : Nat → Nat) (i : Nat) : VG.Proof.X448.Wide.digit f i < VG.Proof.X448.Wide.radix :=
  Nat.mod_lt _ (by decide)

theorem pass_eq (f : Nat → Nat) (n : Nat) :
    VG.Proof.X448.Wide.valN (VG.Proof.X448.Wide.digit f) n + VG.Proof.X448.Wide.radix ^ n * VG.Proof.X448.Wide.carry f n = VG.Proof.X448.Wide.valN f n := by
  induction n with
  | zero => simp only [VG.Proof.X448.Wide.valN, VG.Proof.X448.Wide.carry, Nat.mul_zero, Nat.add_zero]
  | succ n ih =>
    have hd := Nat.mod_add_div (f n + VG.Proof.X448.Wide.carry f n) VG.Proof.X448.Wide.radix
    change VG.Proof.X448.Wide.digit f n + VG.Proof.X448.Wide.radix * VG.Proof.X448.Wide.carry f (n + 1) = f n + VG.Proof.X448.Wide.carry f n at hd
    rw [VG.Proof.X448.Wide.valN, VG.Proof.X448.Wide.valN, Nat.pow_succ, Nat.mul_assoc, Nat.add_assoc, ← Nat.mul_add, hd,
      Nat.mul_add]
    omega

theorem carry_bound {f : Nat → Nat} {n : Nat} (h : ∀ i < n, f i < 2 ^ 118) :
    VG.Proof.X448.Wide.carry f n < 2 ^ 63 := by
  induction n with
  | zero => simp only [VG.Proof.X448.Wide.carry]; decide
  | succ n ih =>
    have hi := ih fun i hi => h i (by omega)
    have hn := h n (by omega)
    simp only [VG.Proof.X448.Wide.carry, VG.Proof.X448.Wide.radix]
    omega

/-- The carry-out folded into the normalized limbs at positions 0 and 4. -/
def folded (f : Nat → Nat) (i : Nat) : Nat :=
  VG.Proof.X448.Wide.digit f i + if i = 0 ∨ i = 4 then VG.Proof.X448.Wide.carry f 8 else 0

theorem folded_val (f : Nat → Nat) :
    VG.Proof.X448.Wide.valN (VG.Proof.X448.Wide.folded f) 8 = VG.Proof.X448.Wide.valN (VG.Proof.X448.Wide.digit f) 8 + (VG.Proof.X448.Wide.half + 1) * VG.Proof.X448.Wide.carry f 8 := by
  change VG.Proof.X448.Wide.valN (fun i => VG.Proof.X448.Wide.digit f i + if i = 0 ∨ i = 4 then VG.Proof.X448.Wide.carry f 8 else 0) 8 = _
  rw [VG.Proof.X448.Wide.valN_add]
  congr 1
  simp only [VG.Proof.X448.Wide.valN, VG.Proof.X448.Wide.half]
  simp (config := {decide := true}) only [ite_true, ite_false, Nat.mul_zero, Nat.add_zero,
    Nat.zero_add, Nat.pow_zero, Nat.one_mul]
  grind

theorem fold_mod (lo hi : Nat) :
    (lo + VG.Proof.X448.Wide.full * hi) % VG.Spec.X448.P = (lo + (VG.Proof.X448.Wide.half + 1) * hi) % VG.Spec.X448.P := by
  rw [VG.Proof.X448.Wide.full_eq, Nat.add_mul, Nat.add_left_comm lo, Nat.add_comm (VG.Spec.X448.P * hi), Nat.add_mul_mod_self_left]

theorem folded_mod (f : Nat → Nat) : VG.Proof.X448.Wide.valN (VG.Proof.X448.Wide.folded f) 8 % VG.Spec.X448.P = VG.Proof.X448.Wide.valN f 8 % VG.Spec.X448.P := by
  rw [VG.Proof.X448.Wide.folded_val, ← VG.Proof.X448.Wide.fold_mod, ← VG.Proof.X448.Wide.pass_eq f 8]
  rfl

theorem folded_bound {f : Nat → Nat} (h : ∀ i < 8, f i < 2 ^ 118) :
    ∀ i < 8, VG.Proof.X448.Wide.folded f i < 2 ^ 118 := by
  have hc := VG.Proof.X448.Wide.carry_bound h
  intro i _
  have hd := VG.Proof.X448.Wide.digit_lt f i
  simp only [VG.Proof.X448.Wide.folded]
  split <;> simp only [VG.Proof.X448.Wide.radix] at hd <;> omega

/-- After two folds, no carry remains beyond the 448-bit field width. -/
theorem final_carry {f : Nat → Nat} (h : ∀ i < 8, f i < 2 ^ 118) :
    VG.Proof.X448.Wide.carry (VG.Proof.X448.Wide.folded (VG.Proof.X448.Wide.folded f)) 8 = 0 := by
  by_contra hn
  have hn : 1 ≤ VG.Proof.X448.Wide.carry (VG.Proof.X448.Wide.folded (VG.Proof.X448.Wide.folded f)) 8 := Nat.pos_of_ne_zero hn
  have c0 := VG.Proof.X448.Wide.carry_bound h
  have v0 := VG.Proof.X448.Wide.valN_lt (n := 8) (fun i _ => VG.Proof.X448.Wide.digit_lt f i)
  have v1 := VG.Proof.X448.Wide.valN_lt (n := 8) (fun i _ => VG.Proof.X448.Wide.digit_lt (VG.Proof.X448.Wide.folded f) i)
  have e1 := VG.Proof.X448.Wide.pass_eq (VG.Proof.X448.Wide.folded f) 8
  have e2 := VG.Proof.X448.Wide.pass_eq (VG.Proof.X448.Wide.folded (VG.Proof.X448.Wide.folded f)) 8
  rw [VG.Proof.X448.Wide.folded_val] at e1 e2
  change VG.Proof.X448.Wide.valN (VG.Proof.X448.Wide.digit f) 8 < VG.Proof.X448.Wide.full at v0
  change VG.Proof.X448.Wide.valN (VG.Proof.X448.Wide.digit (VG.Proof.X448.Wide.folded f)) 8 < VG.Proof.X448.Wide.full at v1
  change VG.Proof.X448.Wide.valN (VG.Proof.X448.Wide.digit (VG.Proof.X448.Wide.folded f)) 8 + VG.Proof.X448.Wide.full * VG.Proof.X448.Wide.carry (VG.Proof.X448.Wide.folded f) 8 = _ at e1
  change VG.Proof.X448.Wide.valN (VG.Proof.X448.Wide.digit (VG.Proof.X448.Wide.folded (VG.Proof.X448.Wide.folded f))) 8 + VG.Proof.X448.Wide.full * VG.Proof.X448.Wide.carry (VG.Proof.X448.Wide.folded (VG.Proof.X448.Wide.folded f)) 8 = _ at e2
  have small : (VG.Proof.X448.Wide.half + 1) * (2 ^ 63 + 1) < VG.Proof.X448.Wide.full := by decide +kernel
  have c1 : VG.Proof.X448.Wide.carry (VG.Proof.X448.Wide.folded f) 8 ≤ 1 := by
    by_contra hc
    have hb := Nat.mul_le_mul_left (VG.Proof.X448.Wide.half + 1) (Nat.le_of_lt c0)
    have hp := Nat.mul_le_mul_left VG.Proof.X448.Wide.full (show 2 ≤ VG.Proof.X448.Wide.carry (VG.Proof.X448.Wide.folded f) 8 from by omega)
    omega
  rcases Nat.eq_zero_or_pos (VG.Proof.X448.Wide.carry (VG.Proof.X448.Wide.folded f) 8) with hc | hc
  · rw [hc, Nat.mul_zero, Nat.add_zero] at e2
    have hp := Nat.mul_le_mul_left VG.Proof.X448.Wide.full hn
    omega
  · have hc : VG.Proof.X448.Wide.carry (VG.Proof.X448.Wide.folded f) 8 = 1 := by omega
    rw [hc, Nat.mul_one] at e1 e2
    have hb := Nat.mul_le_mul_left (VG.Proof.X448.Wide.half + 1) (Nat.le_of_lt c0)
    have hp := Nat.mul_le_mul_left VG.Proof.X448.Wide.full hn
    omega

def normalized (f : Nat → Nat) : Nat → Nat := VG.Proof.X448.Wide.digit (VG.Proof.X448.Wide.folded (VG.Proof.X448.Wide.folded f))

theorem normalized_mod {f : Nat → Nat} (h : ∀ i < 8, f i < 2 ^ 118) :
    VG.Proof.X448.Wide.valN (VG.Proof.X448.Wide.normalized f) 8 % VG.Spec.X448.P = VG.Proof.X448.Wide.valN f 8 % VG.Spec.X448.P := by
  have e := VG.Proof.X448.Wide.pass_eq (VG.Proof.X448.Wide.folded (VG.Proof.X448.Wide.folded f)) 8
  rw [VG.Proof.X448.Wide.final_carry h, Nat.mul_zero, Nat.add_zero] at e
  rw [VG.Proof.X448.Wide.normalized, e, VG.Proof.X448.Wide.folded_mod, VG.Proof.X448.Wide.folded_mod]

end VG.Proof.X448.Wide

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Wide.Product`. -/
section

/-!
# X448: row multiplication and coefficient reduction

Untrusted: everything here is checked by Lean. Multiplication adds one row
at a time to a 16-word coefficient array. The upper coefficients fold
into eight limbs using the field prime's two non-leading terms.
-/

namespace VG.Proof.X448.Wide

open VG.Spec.X448 VG.Proof.X448

def addAt (f : Nat → Nat) (k v : Nat) (i : Nat) : Nat :=
  if i = k then f i + v else f i

theorem addAt_val (f : Nat → Nat) {n k : Nat} (hk : k < n) (v : Nat) :
    VG.Proof.X448.Wide.valN (VG.Proof.X448.Wide.addAt f k v) n = VG.Proof.X448.Wide.valN f n + VG.Proof.X448.Wide.radix ^ k * v :=
  VG.Proof.X448.Wide.valN_update hk (fun _ _ => rfl)

/-- The first `n` products of a row, at displacement `i`. -/
def addRow (f : Nat → Nat) (a : Nat) (g : Nat → Nat) (i : Nat) : Nat → Nat → Nat
  | 0 => f
  | n + 1 => VG.Proof.X448.Wide.addAt (VG.Proof.X448.Wide.addRow f a g i n) (i + n) (a * g n)

theorem addRow_val (f g : Nat → Nat) (a : Nat) {i n : Nat} (h : i + n ≤ 16) :
    VG.Proof.X448.Wide.valN (VG.Proof.X448.Wide.addRow f a g i n) 16 = VG.Proof.X448.Wide.valN f 16 + VG.Proof.X448.Wide.radix ^ i * a * VG.Proof.X448.Wide.valN g n := by
  induction n with
  | zero => simp only [VG.Proof.X448.Wide.addRow, VG.Proof.X448.Wide.valN, Nat.mul_zero, Nat.add_zero]
  | succ n ih =>
    rw [VG.Proof.X448.Wide.addRow, VG.Proof.X448.Wide.addAt_val _ (by omega), ih (by omega), VG.Proof.X448.Wide.valN_succ g n, Nat.pow_add]
    generalize VG.Proof.X448.Wide.radix ^ i = A
    generalize VG.Proof.X448.Wide.radix ^ n = B
    grind

theorem addRow_at (f g : Nat → Nat) (a i n k : Nat) :
    VG.Proof.X448.Wide.addRow f a g i n k = f k + if i ≤ k ∧ k < i + n then a * g (k - i) else 0 := by
  induction n with
  | zero => simp only [VG.Proof.X448.Wide.addRow, Nat.add_zero, show ¬ (i ≤ k ∧ k < i) by omega,
      ite_false, Nat.add_zero]
  | succ n ih =>
    simp only [VG.Proof.X448.Wide.addRow, VG.Proof.X448.Wide.addAt]
    by_cases hk : k = i + n
    · subst k
      rw [ite_eq_left rfl, ih, ite_eq_right (by omega), Nat.add_zero,
        ite_eq_left (by omega), Nat.add_sub_cancel_left]
    · rw [ite_eq_right hk, ih]
      have he : (i ≤ k ∧ k < i + n) ↔ (i ≤ k ∧ k < i + (n + 1)) := by omega
      simp only [he]

/-- The first `n` rows of the product of two eight-limb operands. -/
def rows (f g : Nat → Nat) : Nat → Nat → Nat
  | 0 => fun _ => 0
  | n + 1 => VG.Proof.X448.Wide.addRow (VG.Proof.X448.Wide.rows f g n) (f n) g n 8

theorem rows_val (f g : Nat → Nat) {n : Nat} (hn : n ≤ 8) :
    VG.Proof.X448.Wide.valN (VG.Proof.X448.Wide.rows f g n) 16 = VG.Proof.X448.Wide.valN f n * VG.Proof.X448.Wide.valN g 8 := by
  induction n with
  | zero => simp only [VG.Proof.X448.Wide.rows, VG.Proof.X448.Wide.valN, Nat.mul_zero, Nat.zero_add, Nat.zero_mul]
  | succ n ih =>
    rw [VG.Proof.X448.Wide.rows, VG.Proof.X448.Wide.addRow_val _ _ _ (by omega), ih (by omega), VG.Proof.X448.Wide.valN_succ f n, Nat.add_mul]

theorem rows_bound {f g : Nat → Nat} (hf : ∀ i < 8, f i < VG.Proof.X448.Wide.radix)
    (hg : ∀ i < 8, g i < VG.Proof.X448.Wide.radix) {n : Nat} (hn : n ≤ 8) (k : Nat) :
    VG.Proof.X448.Wide.rows f g n k ≤ n * (VG.Proof.X448.Wide.radix - 1) ^ 2 := by
  induction n with
  | zero => simp only [VG.Proof.X448.Wide.rows, Nat.zero_mul, Nat.le_refl]
  | succ n ih =>
    rw [VG.Proof.X448.Wide.rows, VG.Proof.X448.Wide.addRow_at]
    have hp := ih (by omega)
    split
    · rename_i hk
      have h1 := hf n (by omega)
      have h2 := hg (k - n) (by omega)
      have hprod : f n * g (k - n) ≤ (VG.Proof.X448.Wide.radix - 1) ^ 2 := by
        rw [Nat.pow_two]
        exact Nat.mul_le_mul (by omega) (by omega)
      rw [Nat.succ_mul]; omega
    · rw [Nat.succ_mul]; omega

/-- Coefficients of degree 8–11 fold once; 12–15 fold twice. -/
def reduced (f : Nat → Nat) (k : Nat) : Nat :=
  f k + f (k + 8) + if k < 4 then f (k + 12) else f (k + 4) + f (k + 8)

theorem reduced_val (f : Nat → Nat) :
    VG.Proof.X448.Wide.valN (VG.Proof.X448.Wide.reduced f) 8 =
      (VG.Proof.X448.Wide.valN f 4 + VG.Proof.X448.Wide.valN (fun i => f (8 + i)) 4 + VG.Proof.X448.Wide.valN (fun i => f (12 + i)) 4) +
      VG.Proof.X448.Wide.half * (VG.Proof.X448.Wide.valN (fun i => f (4 + i)) 4 + VG.Proof.X448.Wide.valN (fun i => f (12 + i)) 4 +
        VG.Proof.X448.Wide.valN (fun i => f (8 + i)) 4 + VG.Proof.X448.Wide.valN (fun i => f (12 + i)) 4) := by
  rw [show 8 = 4 + 4 from rfl, VG.Proof.X448.Wide.valN_split]
  apply congrArg₂ (· + ·)
  · rw [← VG.Proof.X448.Wide.valN_add, ← VG.Proof.X448.Wide.valN_add]
    apply VG.Proof.X448.Wide.valN_congr
    intro i hi
    simp only [VG.Proof.X448.Wide.reduced, ite_eq_left hi, Nat.add_comm i]
  · apply congrArg (VG.Proof.X448.Wide.radix ^ 4 * ·)
    rw [← VG.Proof.X448.Wide.valN_add, ← VG.Proof.X448.Wide.valN_add, ← VG.Proof.X448.Wide.valN_add]
    apply VG.Proof.X448.Wide.valN_congr
    intro i _
    simp only [VG.Proof.X448.Wide.reduced, ite_eq_right (by omega : ¬ 4 + i < 4)]
    rw [show 4 + i + 8 = 12 + i by omega, show 4 + i + 4 = 8 + i by omega]
    simp only [Nat.reduceAdd]
    omega

theorem reduced_mod (f : Nat → Nat) : VG.Proof.X448.Wide.valN (VG.Proof.X448.Wide.reduced f) 8 % VG.Spec.X448.P = VG.Proof.X448.Wide.valN f 16 % VG.Spec.X448.P := by
  have hp : VG.Spec.X448.P = VG.Proof.X448.Wide.full - VG.Proof.X448.Wide.half - 1 := by decide +kernel
  have he : VG.Proof.X448.Wide.valN f 16 = VG.Proof.X448.Wide.valN (VG.Proof.X448.Wide.reduced f) 8 +
      VG.Spec.X448.P * (VG.Proof.X448.Wide.valN (fun i => f (8 + i)) 4 + (VG.Proof.X448.Wide.half + 1) * VG.Proof.X448.Wide.valN (fun i => f (12 + i)) 4) := by
    rw [VG.Proof.X448.Wide.reduced_val, show 16 = 8 + 8 from rfl, VG.Proof.X448.Wide.valN_split,
      show 8 = 4 + 4 from rfl, VG.Proof.X448.Wide.valN_split, VG.Proof.X448.Wide.valN_split]
    simp only [← Nat.add_assoc, Nat.reduceAdd]
    simp only [hp, VG.Proof.X448.Wide.full, VG.Proof.X448.Wide.half, VG.Proof.X448.Wide.radix, Nat.reducePow]
    omega
  rw [he, Nat.add_mul_mod_self_left]

theorem reduced_bound {f : Nat → Nat} (h : ∀ i < 16, f i < 2 ^ 116) :
    ∀ i < 8, VG.Proof.X448.Wide.reduced f i < 2 ^ 118 := by
  intro i hi
  have h0 := h i (by omega)
  have h1 := h (i + 8) (by omega)
  simp only [VG.Proof.X448.Wide.reduced]
  split
  · have h2 := h (i + 12) (by omega); omega
  · have h2 := h (i + 4) (by omega); omega

/-- A product coefficient accumulated along its diagonal. -/
def colSum (f g : Nat → Nat) (k : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => VG.Proof.X448.Wide.colSum f g k n + if n ≤ k ∧ k < n + 8 then f n * g (k - n) else 0

theorem colSum_eq (f g : Nat → Nat) (k n : Nat) :
    VG.Proof.X448.Wide.colSum f g k n = VG.Proof.X448.Wide.rows f g n k := by
  induction n with
  | zero => rfl
  | succ n ih => rw [VG.Proof.X448.Wide.colSum, VG.Proof.X448.Wide.rows, VG.Proof.X448.Wide.addRow_at, ih]

theorem rows_congr {f g f' g' : Nat → Nat} (hf : ∀ i < 8, f i = f' i)
    (hg : ∀ i < 8, g i = g' i) {n : Nat} (hn : n ≤ 8) (k : Nat) :
    VG.Proof.X448.Wide.rows f g n k = VG.Proof.X448.Wide.rows f' g' n k := by
  rw [← VG.Proof.X448.Wide.colSum_eq, ← VG.Proof.X448.Wide.colSum_eq]
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [VG.Proof.X448.Wide.colSum, VG.Proof.X448.Wide.colSum, ih (by omega)]
    split
    · rename_i h
      rw [hf n (by omega), hg (k - n) (by omega)]
    · rfl

end VG.Proof.X448.Wide

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Wide.Word`. -/
section

/-! Untrusted: two-word arithmetic for radix-2⁵⁶ X448 coefficients. -/
namespace VG.Proof.X448.Wide

open VG VG.AArch64 VG.Proof.Ed25519.Word64
open VG.Proof.Ed25519.AArch64 (mulHi mul_lo_hi)

/-- The value of a two-word coefficient. -/
def pair (lo hi : BitVec 64) : Nat := lo.toNat + 2 ^ 64 * hi.toNat

/-- A multiply-add below 2¹²⁸ cannot lose a high carry. -/
theorem madd128 (a b lo hi : BitVec 64)
    (h : a.toNat * b.toNat + VG.Proof.X448.Wide.pair lo hi < 2 ^ 128) :
    VG.Proof.X448.Wide.pair (addCarry lo (a * b) false)
      (addCarry hi (mulHi a b) (carryOut lo (a * b) false)) =
      a.toNat * b.toNat + VG.Proof.X448.Wide.pair lo hi := by
  have e0 := addCarry_value lo (a * b) false
  have e1 := addCarry_value hi (mulHi a b) (carryOut lo (a * b) false)
  have em := mul_lo_hi a b
  have hc := Bool.toNat_le (carryOut hi (mulHi a b) (carryOut lo (a * b) false))
  simp only [Bool.toNat_false, Nat.add_zero] at e0
  simp only [VG.Proof.X448.Wide.pair] at h ⊢
  omega

/-- Adding a one-word carry to a coefficient also preserves its value. -/
theorem add128 (lo hi c : BitVec 64) (h : VG.Proof.X448.Wide.pair lo hi + c.toNat < 2 ^ 128) :
    VG.Proof.X448.Wide.pair (addCarry lo c false) (addCarry hi 0 (carryOut lo c false)) =
      VG.Proof.X448.Wide.pair lo hi + c.toNat := by
  have e0 := addCarry_value lo c false
  have e1 := addCarry_value hi 0 (carryOut lo c false)
  simp only [Bool.toNat_false, Nat.add_zero, show (0 : BitVec 64).toNat = 0 from rfl] at e0 e1
  simp only [VG.Proof.X448.Wide.pair] at h ⊢
  omega

/-- Addition of two coefficients below the two-word capacity. -/
theorem addPair128 (lo hi a b : BitVec 64) (h : VG.Proof.X448.Wide.pair lo hi + VG.Proof.X448.Wide.pair a b < 2 ^ 128) :
    VG.Proof.X448.Wide.pair (addCarry lo a false) (addCarry hi b (carryOut lo a false)) =
      VG.Proof.X448.Wide.pair lo hi + VG.Proof.X448.Wide.pair a b := by
  have e0 := addCarry_value lo a false
  have e1 := addCarry_value hi b (carryOut lo a false)
  simp only [Bool.toNat_false, Nat.add_zero] at e0
  simp only [VG.Proof.X448.Wide.pair] at h ⊢
  omega

/-- The low 56-bit digit of a coefficient. -/
theorem low56 (lo hi : BitVec 64) :
    (lo &&& BitVec.ofNat 64 (2 ^ 56 - 1)).toNat = VG.Proof.X448.Wide.pair lo hi % VG.Proof.X448.Wide.radix := by
  rw [BitVec.toNat_and, show (BitVec.ofNat 64 (2 ^ 56 - 1)).toNat = 2 ^ 56 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod]
  simp only [VG.Proof.X448.Wide.pair, VG.Proof.X448.Wide.radix]
  omega

/-- The upper coefficient bits fit in one word after a 56-bit carry step. -/
theorem high56 (lo hi : BitVec 64) (h : VG.Proof.X448.Wide.pair lo hi < 2 ^ 119) :
    ((lo >>> 56) + (hi <<< 8)).toNat = VG.Proof.X448.Wide.pair lo hi / VG.Proof.X448.Wide.radix := by
  have hh : hi.toNat < 2 ^ 55 := by simp only [VG.Proof.X448.Wide.pair] at h; omega
  rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  simp only [VG.Proof.X448.Wide.pair, VG.Proof.X448.Wide.radix]
  have hl := lo.isLt
  omega

end VG.Proof.X448.Wide

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Wide.Term`. -/
section

/-! Untrusted: the register-only multiply-add used by wide X448 columns. -/
namespace VG.Proof.X448.Wide

open VG VG.AArch64 VG.Impl.X448.AArch64.Wide VG.Proof.Ed25519.Word64
open VG.Proof.Ed25519.AArch64 (mulHi read_x)
open VG.Proof.X448.AArch64 (Keeps)

theorem term_ok (s : State)
    (h : (s.gpr .x6).toNat * (s.gpr .x9).toNat + VG.Proof.X448.Wide.pair (s.gpr .x4) (s.gpr .x5) < 2 ^ 128) :
    WP isa (.block term) s fun t =>
      VG.Proof.X448.Wide.pair (t.gpr .x4) (t.gpr .x5) =
        (s.gpr .x6).toNat * (s.gpr .x9).toNat + VG.Proof.X448.Wide.pair (s.gpr .x4) (s.gpr .x5) ∧
      t.mem = s.mem ∧ Keeps [.x4, .x5, .x10, .x11] s t := by
  apply WP.of_runBlock
  simp only [term, termFrom, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry,
    BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, rfl, (fun r hr => ?_), rfl, rfl⟩
  · have hm := VG.Proof.X448.Wide.madd128 (s.gpr .x6) (s.gpr .x9) (s.gpr .x4) (s.gpr .x5) h
    dsimp only [addCarry, carryOut, mulHi, Size.bits] at hm ⊢
    exact hm
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr, ite_false]

theorem termFrom_ok (s : State) (a b : Reg)
    (ha : a ≠ .x10) (hb : b ≠ .x10)
    (h : (s.gpr a).toNat * (s.gpr b).toNat + VG.Proof.X448.Wide.pair (s.gpr .x4) (s.gpr .x5) < 2 ^ 128) :
    WP isa (.block (termFrom a b)) s fun t =>
      VG.Proof.X448.Wide.pair (t.gpr .x4) (t.gpr .x5) =
        (s.gpr a).toNat * (s.gpr b).toNat + VG.Proof.X448.Wide.pair (s.gpr .x4) (s.gpr .x5) ∧
      t.mem = s.mem ∧ Keeps [.x4, .x5, .x10, .x11] s t := by
  apply WP.of_runBlock
  simp only [termFrom, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry,
    BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, ha, hb,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, rfl, (fun r hr => ?_), rfl, rfl⟩
  · have hm := VG.Proof.X448.Wide.madd128 (s.gpr a) (s.gpr b) (s.gpr .x4) (s.gpr .x5) h
    dsimp only [addCarry, carryOut, mulHi, Size.bits] at hm ⊢
    exact hm
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr, ite_false]

end VG.Proof.X448.Wide

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Wide.CacheRegs`. -/
section

/-! Untrusted: register allocation for cached wide X448 operands. -/
namespace VG.Proof.X448.Wide

open VG VG.AArch64
open VG.Impl.X448.AArch64.Cached
open VG.Proof.X448.AArch64 (Keeps)

abbrev termRegs : List Reg := [.x4, .x5, .x10, .x11]

def sqrRegs : List Reg := [.x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x13, .x14, .x15, .x16]

theorem cacheReg_kept {i : Nat} (hi : i < 8) : cacheReg i ∉ ([.x4, .x5, .x10, .x11] : List Reg) := by
  have h : ∀ n < 8, cacheReg n ∉ ([.x4, .x5, .x10, .x11] : List Reg) := by decide +kernel
  exact h i hi

theorem cacheReg_member {i : Nat} (hi : i < 8) : cacheReg i ∈ VG.Proof.X448.Wide.sqrRegs := by
  have h : ∀ n < 8, cacheReg n ∈ VG.Proof.X448.Wide.sqrRegs := by decide +kernel
  exact h i hi

theorem cacheReg_ne10 {i : Nat} (hi : i < 8) : cacheReg i ≠ .x10 := by
  intro h
  exact VG.Proof.X448.Wide.cacheReg_kept hi (by rw [h]; decide)

theorem cacheReg_ne11 {i : Nat} (hi : i < 8) : cacheReg i ≠ .x11 := by
  intro h
  exact VG.Proof.X448.Wide.cacheReg_kept hi (by rw [h]; decide)

theorem cacheReg_ne3 (i : Nat) : cacheReg i ≠ .x3 := by
  unfold cacheReg
  split <;> decide

theorem cacheReg_inj {i j : Nat} (hi : i < 8) (hj : j < 8) : cacheReg i = cacheReg j ↔ i = j := by
  have h : ∀ i < 8, ∀ j < 8, cacheReg i = cacheReg j ↔ i = j := by decide +kernel
  exact h i hi j hj

end VG.Proof.X448.Wide

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Wide.Memory`. -/
section

/-! Untrusted: two-word coefficients in the existing X448 scratch region. -/
namespace VG.Proof.X448.Wide

open VG VG.AArch64 VG.Proof.X448.AArch64

abbrev coeff (m : Mem) (base : Addr) (o i : Nat) : Nat :=
  VG.Proof.X448.Wide.pair (word m base (o + 16 * i)) (word m base (o + 16 * i + 8))

def putCoeff (m : Mem) (base : Addr) (o i : Nat) (lo hi : BitVec 64) : Mem :=
  (m.writeW (off base (o + 16 * i)) lo).writeW (off base (o + 16 * i + 8)) hi

theorem putCoeff_outside (m : Mem) (base : Addr) {o i : Nat} (lo hi : BitVec 64)
    (h : o + 16 * i + 16 ≤ 8192) :
    Outside base (o + 16 * i) 16 m (VG.Proof.X448.Wide.putCoeff m base o i lo hi) := by
  exact ((writeW_outside m base lo (by omega)).mono (by omega) (by omega)).trans
    ((writeW_outside _ base hi (by omega)).mono (by omega) (by omega))

theorem coeff_put (m : Mem) (base : Addr) {o i j : Nat} (lo hi : BitVec 64)
    (hi' : o + 16 * i + 16 ≤ 8192) (hj : o + 16 * j + 16 ≤ 8192) :
    VG.Proof.X448.Wide.coeff (VG.Proof.X448.Wide.putCoeff m base o i lo hi) base o j =
      if j = i then VG.Proof.X448.Wide.pair lo hi else VG.Proof.X448.Wide.coeff m base o j := by
  unfold VG.Proof.X448.Wide.coeff VG.Proof.X448.Wide.putCoeff
  have e0 : o + 16 * i = o + 8 * (2 * i) := by omega
  have e1 : o + 16 * i + 8 = o + 8 * (2 * i + 1) := by omega
  have e2 : o + 16 * j = o + 8 * (2 * j) := by omega
  have e3 : o + 16 * j + 8 = o + 8 * (2 * j + 1) := by omega
  rw [e1, e0, e3, e2]
  rw [word_write _ base (by omega) (by omega), word_write _ base (by omega) (by omega)]
  rw [ite_eq_right (by omega : 2 * j ≠ 2 * i + 1)]
  rw [word_write _ base (by omega) (by omega)]
  by_cases h : j = i
  · subst j
    simp only [ite_true]
  · simp only [h, show 2 * j ≠ 2 * i by omega, show 2 * j + 1 ≠ 2 * i + 1 by omega,
      ite_false]
    rw [word_write _ base (by omega) (by omega), ite_eq_right (by omega : 2 * j + 1 ≠ 2 * i)]

theorem outside_coeff {base : Addr} {o n d : Nat} {m m' : Mem}
    (h : Outside base o n m m') (hd : d + 16 ≤ o ∨ o + n ≤ d)
    (hd' : d + 16 ≤ 8192) :
    VG.Proof.X448.Wide.pair (word m' base d) (word m' base (d + 8)) =
      VG.Proof.X448.Wide.pair (word m base d) (word m base (d + 8)) := by
  rw [h.word (by omega) (by omega), h.word (by omega) (by omega)]

end VG.Proof.X448.Wide

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Wide.Column`. -/
section

/-! Untrusted: a diagonal of an eight-by-eight product, accumulated in registers. -/
namespace VG.Proof.X448.Wide

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld st ACC)
open VG.Impl.X448.AArch64.Wide VG.Proof.X448.AArch64

/-- Load one pair of operands without changing the coefficient registers. -/
theorem loadTerm_ok {s : State} {base : Addr} (hs : Scr s base) {a b i j : Nat}
    (ha : a + 64 ≤ 8192) (hb : b + 64 ≤ 8192)
    (ha8 : a % 8 = 0) (hb8 : b % 8 = 0) (hi : i < 8) (hj : j < 8) :
    WP isa (.block [ld .x6 (a + 8 * i), ld .x9 (b + 8 * j)]) s fun t =>
      t.gpr .x6 = word s.mem base (a + 8 * i) ∧
      t.gpr .x9 = word s.mem base (b + 8 * j) ∧
      t.mem = s.mem ∧ Keeps [.x6, .x9] s t := by
  have ae : (a + 8 * i) % 8 = 0 ∧ a + 8 * i < 32768 := ⟨by omega, by omega⟩
  have be : (b + 8 * j) % 8 = 0 ∧ b + 8 * j < 32768 := ⟨by omega, by omega⟩
  have al := hs.read (d := a + 8 * i) (n := 8) (by omega)
  have bl := hs.read (d := b + 8 * j) (n := 8) (by omega)
  apply WP.of_runBlock
  simp only [ld, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
    ae, be, and_self, State.load, hs.x3, al, bl, ite_true, Option.map_some,
    Option.bind_some, BitVec.setWidth_eq, read8_eq, RegUpd.gpr_write,
    ite_false, reduceCtorEq, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

/-- Initialize a register coefficient to zero. -/
theorem zero_ok (s : State) :
    WP isa (.block [.movz .x .x4 0 0, .movz .x .x5 0 0]) s fun t =>
      VG.Proof.X448.Wide.pair (t.gpr .x4) (t.gpr .x5) = 0 ∧ t.mem = s.mem ∧ Keeps [.x4, .x5] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, show 16 * 0 < Size.x.bits from by decide, ite_true, RegUpd.gpr_write, BitVec.setWidth_eq, ite_false,
    reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

/-- Write the two coefficient words. -/
theorem store_ok {s : State} {base : Addr} (hs : Scr s base) {k : Nat} (hk : k < 16) :
    WP isa (.block [st .x4 (ACC + 16 * k), st .x5 (ACC + 16 * k + 8)]) s fun t =>
      t.mem = VG.Proof.X448.Wide.putCoeff s.mem base ACC k (s.gpr .x4) (s.gpr .x5) ∧ Keeps [] s t := by
  have ae : (ACC + 16 * k) % 8 = 0 ∧ ACC + 16 * k < 32768 := by simp only [ACC]; omega
  have be : (ACC + 16 * k + 8) % 8 = 0 ∧ ACC + 16 * k + 8 < 32768 := by simp only [ACC]; omega
  have aw := hs.write (d := ACC + 16 * k) (n := 8) (by simp only [ACC]; omega)
  have bw := hs.write (d := ACC + 16 * k + 8) (n := 8) (by simp only [ACC]; omega)
  apply WP.of_runBlock
  simp only [st, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
    ae, be, and_self, State.read, State.store, hs.x3, aw, bw, ite_true,
    Option.bind_some, BitVec.setWidth_eq, write8_eq,
    Option.some.injEq, exists_eq_left']
  exact ⟨rfl, (fun _ _ => rfl), rfl, rfl⟩

def colRegs : List Reg := [.x4, .x5, .x6, .x9, .x10, .x11]

theorem columnBody_ok {s : State} {base : Addr} (hs : Scr s base) {a b k : Nat}
    (ha : a + 64 ≤ 8192) (hb : b + 64 ≤ 8192)
    (ha8 : a % 8 = 0) (hb8 : b % 8 = 0)
    (fa : ∀ i < 8, limbs s.mem base a i < VG.Proof.X448.Wide.radix)
    (fb : ∀ i < 8, limbs s.mem base b i < VG.Proof.X448.Wide.radix)
    (hz : VG.Proof.X448.Wide.pair (s.gpr .x4) (s.gpr .x5) = 0) :
    WP isa (.block ((List.range 8).flatMap (fun i => if i ≤ k ∧ k < i + 8 then
      [ld .x6 (a + 8 * i), ld .x9 (b + 8 * (k - i))] ++ term else []))) s fun t =>
      VG.Proof.X448.Wide.pair (t.gpr .x4) (t.gpr .x5) = VG.Proof.X448.Wide.rows (limbs s.mem base a) (limbs s.mem base b) 8 k ∧
      t.mem = s.mem ∧ Keeps VG.Proof.X448.Wide.colRegs s t := by
  let f := limbs s.mem base a
  let g := limbs s.mem base b
  let inv := fun n (t : State) =>
    VG.Proof.X448.Wide.pair (t.gpr .x4) (t.gpr .x5) = VG.Proof.X448.Wide.colSum f g k n ∧
    t.mem = s.mem ∧ Keeps VG.Proof.X448.Wide.colRegs s t
  have step : ∀ n t, n < 8 → inv n t →
      WP isa (.block (if n ≤ k ∧ k < n + 8 then
        [ld .x6 (a + 8 * n), ld .x9 (b + 8 * (k - n))] ++ term else [])) t (inv (n + 1)) := by
    intro n t hn ⟨tv, tm, tk⟩
    by_cases h : n ≤ k ∧ k < n + 8
    · rw [ite_eq_left h, WP.block_append_iff]
      have ts := hs.of_keeps tk (by decide)
      refine WP.mono (VG.Proof.X448.Wide.loadTerm_ok ts ha hb ha8 hb8 hn (by omega)) fun u ⟨u6, u9, um, uk⟩ => ?_
      have uv : VG.Proof.X448.Wide.pair (u.gpr .x4) (u.gpr .x5) = VG.Proof.X448.Wide.colSum f g k n := by
        rw [uk.1 .x4 (by decide), uk.1 .x5 (by decide), tv]
      have av : (u.gpr .x6).toNat = f n := by rw [u6, tm]
      have bv : (u.gpr .x9).toNat = g (k - n) := by rw [u9, tm]
      have prod : f n * g (k - n) ≤ (VG.Proof.X448.Wide.radix - 1) ^ 2 := by
        rw [Nat.pow_two]
        exact Nat.mul_le_mul (by have fh : f n < VG.Proof.X448.Wide.radix := fa n hn; omega) (by have gh : g (k - n) < VG.Proof.X448.Wide.radix := fb (k - n) (by omega); omega)
      have cb := VG.Proof.X448.Wide.rows_bound fa fb (n := n) (by omega) k
      rw [← VG.Proof.X448.Wide.colSum_eq] at cb
      change VG.Proof.X448.Wide.colSum f g k n ≤ n * (VG.Proof.X448.Wide.radix - 1) ^ 2 at cb
      have sum : (u.gpr .x6).toNat * (u.gpr .x9).toNat + VG.Proof.X448.Wide.pair (u.gpr .x4) (u.gpr .x5) < 2 ^ 128 := by
        rw [av, bv, uv]
        have bd : (n + 1) * (VG.Proof.X448.Wide.radix - 1) ^ 2 ≤ 8 * (VG.Proof.X448.Wide.radix - 1) ^ 2 :=
          Nat.mul_le_mul_right _ (by omega)
        have cap : 8 * (VG.Proof.X448.Wide.radix - 1) ^ 2 < 2 ^ 128 := by decide +kernel
        rw [Nat.add_mul, Nat.one_mul] at bd
        omega
      refine WP.mono (VG.Proof.X448.Wide.term_ok u sum) fun v ⟨vv, vm, vk⟩ => ?_
      refine ⟨?_, vm.trans (um.trans tm), ?_⟩
      · rw [vv, av, bv, uv, VG.Proof.X448.Wide.colSum, ite_eq_left h]
        omega
      · exact tk.trans ((uk.mono (by decide)).trans (vk.mono (by decide)))
    · rw [ite_eq_right h]
      apply WP.block_nil
      exact ⟨by rw [VG.Proof.X448.Wide.colSum, ite_eq_right h, Nat.add_zero]; exact tv, tm, tk⟩
  have init : inv 0 s := ⟨hz, rfl, Keeps.refl _ _⟩
  refine WP.mono (wp_range_flatMap (M := isa) (N := 8) inv step 8 (by decide) s init)
    fun t ⟨tv, tm, tk⟩ => ?_
  exact ⟨tv.trans (VG.Proof.X448.Wide.colSum_eq f g k 8), tm, tk⟩

theorem column_ok {s : State} {base : Addr} (hs : Scr s base) {a b k : Nat}
    (ha : a + 64 ≤ 8192) (hb : b + 64 ≤ 8192)
    (ha8 : a % 8 = 0) (hb8 : b % 8 = 0) (hk : k < 16)
    (fa : ∀ i < 8, limbs s.mem base a i < VG.Proof.X448.Wide.radix)
    (fb : ∀ i < 8, limbs s.mem base b i < VG.Proof.X448.Wide.radix) :
    WP isa (.block (column a b k)) s fun t =>
      VG.Proof.X448.Wide.coeff t.mem base ACC k = VG.Proof.X448.Wide.rows (limbs s.mem base a) (limbs s.mem base b) 8 k ∧
      Outside base (ACC + 16 * k) 16 s.mem t.mem ∧ Keeps VG.Proof.X448.Wide.colRegs s t := by
  rw [column, List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Wide.zero_ok s) fun u ⟨uz, um, uk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Wide.columnBody_ok (hs.of_keeps uk (by decide)) ha hb ha8 hb8
    (by rw [um]; exact fa) (by rw [um]; exact fb) uz) fun v ⟨vv, vm, vk⟩ => ?_
  have vs := (hs.of_keeps uk (by decide)).of_keeps vk (by decide)
  refine WP.mono (VG.Proof.X448.Wide.store_ok vs hk) fun t ⟨tm, tk⟩ => ?_
  refine ⟨?_, ?_, ?_⟩
  · rw [tm, VG.Proof.X448.Wide.coeff_put _ base _ _ (by simp only [ACC]; omega)
      (by simp only [ACC]; omega), ite_eq_left rfl, vv, um]
  · rw [tm, vm, um]
    exact VG.Proof.X448.Wide.putCoeff_outside _ _ _ _ (by simp only [ACC]; omega)
  · exact (uk.mono (by decide)).trans (vk.trans (tk.mono (by decide)))

end VG.Proof.X448.Wide

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Wide.LoadCached`. -/
section

/-! Untrusted: load eight wide limbs into the cached operand registers. -/
namespace VG.Proof.X448.Wide

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld)
open VG.Impl.X448.AArch64.Cached VG.Proof.X448.AArch64

theorem cacheLoadStep_ok {s : State} {base : Addr} (hs : Scr s base) {a i : Nat}
    (ha : a + 64 ≤ 8192) (ha8 : a % 8 = 0) (hi : i < 8) :
    WP isa (.block [ld (cacheReg i) (a + 8 * i)]) s fun t =>
      t.gpr (cacheReg i) = word s.mem base (a + 8 * i) ∧
      t.mem = s.mem ∧ Keeps [cacheReg i] s t := by
  have ae : (a + 8 * i) % 8 = 0 ∧ a + 8 * i < 32768 := ⟨by omega, by omega⟩
  have al := hs.read (d := a + 8 * i) (n := 8) (by omega)
  apply WP.of_runBlock
  simp only [ld, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
    ae, and_self, State.load, hs.x3, al, ite_true, Option.map_some,
    Option.bind_some, BitVec.setWidth_eq, read8_eq, RegUpd.gpr_write,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, rfl, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

theorem loadCached_ok {s : State} {base : Addr} (hs : Scr s base) {a : Nat}
    (ha : a + 64 ≤ 8192) (ha8 : a % 8 = 0) :
    WP isa (.block (loadCached a)) s fun t =>
      (∀ i < 8, t.gpr (cacheReg i) = word s.mem base (a + 8 * i)) ∧
      t.mem = s.mem ∧ Keeps VG.Proof.X448.Wide.sqrRegs s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, t.gpr (cacheReg i) = word s.mem base (a + 8 * i)) ∧
    t.mem = s.mem ∧ Keeps VG.Proof.X448.Wide.sqrRegs s t
  have step : ∀ n t, n < 8 → inv n t →
      WP isa (.block [ld (cacheReg n) (a + 8 * n)]) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    refine WP.mono (VG.Proof.X448.Wide.cacheLoadStep_ok (hs.of_keeps tk (by decide)) ha ha8 hn) fun u ⟨uf, um, uk⟩ => ?_
    refine ⟨?_, um.trans tm, tk.trans (uk.mono (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r; exact VG.Proof.X448.Wide.cacheReg_member hn))⟩
    intro i hi
    by_cases h : i = n
    · subst i; rw [uf, tm]
    · rw [uk.1 _ (by
        simp only [List.mem_singleton]
        intro e; exact h ((VG.Proof.X448.Wide.cacheReg_inj (by omega) hn).1 e))]
      exact tf i (by omega)
  exact wp_range_flatMap (M := isa) (N := 8) inv step 8 (by decide) s
    ⟨fun _ hi => by omega, rfl, Keeps.refl _ _⟩

end VG.Proof.X448.Wide

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Wide.SquareProduct`. -/
section

/-! Untrusted: symmetric diagonal accumulation for an eight-limb square. -/
namespace VG.Proof.X448.Wide

def sqrSum (f : Nat → Nat) (k : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => VG.Proof.X448.Wide.sqrSum f k n + if n ≤ k ∧ k < n + 8 ∧ n ≤ k - n then
      if n = k - n then f n * f (k - n) else 2 * (f n * f (k - n)) else 0

theorem sqrSum_eq (f : Nat → Nat) {k : Nat} (hk : k < 16) :
    VG.Proof.X448.Wide.sqrSum f k 8 = VG.Proof.X448.Wide.rows f f 8 k := by
  rw [← VG.Proof.X448.Wide.colSum_eq]
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨
    k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 := by omega
  all_goals (simp [VG.Proof.X448.Wide.sqrSum, VG.Proof.X448.Wide.colSum] <;> grind)

theorem sqrSum_le {n m : Nat} (hn : n ≤ m) (f : Nat → Nat) (k : Nat) :
    VG.Proof.X448.Wide.sqrSum f k n ≤ VG.Proof.X448.Wide.sqrSum f k m := by
  induction m generalizing n with
  | zero =>
    obtain rfl : n = 0 := by omega
    exact Nat.le_refl _
  | succ m ih =>
    by_cases h : n = m + 1
    · subst n; exact Nat.le_refl _
    · exact Nat.le_trans (ih (by omega)) (by rw [VG.Proof.X448.Wide.sqrSum]; omega)

theorem sqrSum_bound {f : Nat → Nat} (hf : ∀ i < 8, f i < VG.Proof.X448.Wide.radix)
    {n k : Nat} (hn : n ≤ 8) (hk : k < 16) : VG.Proof.X448.Wide.sqrSum f k n < 2 ^ 116 := by
  have h := VG.Proof.X448.Wide.sqrSum_le hn f k
  rw [VG.Proof.X448.Wide.sqrSum_eq f hk] at h
  exact Nat.lt_of_le_of_lt (Nat.le_trans h (VG.Proof.X448.Wide.rows_bound hf hf (by decide) k)) (by decide)

end VG.Proof.X448.Wide

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Wide.DoubleTerm`. -/
section

/-! Untrusted: one doubled cross product in symmetric X448 squaring. -/
namespace VG.Proof.X448.Wide

open VG VG.AArch64 VG.Proof.Ed25519.Word64
open VG.Proof.Ed25519.AArch64 (mulHi read_x)
open VG.Proof.X448.AArch64 (Keeps)
open VG.Impl.X448.AArch64.Wide

theorem termFromDouble_ok (s : State) (a b : Reg) (hb : b ≠ .x10) (hb11 : b ≠ .x11)
    (ha : (s.gpr a).toNat < 2 ^ 63)
    (h : 2 * ((s.gpr a).toNat * (s.gpr b).toNat) + VG.Proof.X448.Wide.pair (s.gpr .x4) (s.gpr .x5) < 2 ^ 128) :
    WP isa (.block (termFromDouble a b)) s fun t =>
      VG.Proof.X448.Wide.pair (t.gpr .x4) (t.gpr .x5) =
        2 * ((s.gpr a).toNat * (s.gpr b).toNat) + VG.Proof.X448.Wide.pair (s.gpr .x4) (s.gpr .x5) ∧
      t.mem = s.mem ∧ Keeps [.x4, .x5, .x10, .x11] s t := by
  apply WP.of_runBlock
  simp only [termFromDouble, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry,
    BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, hb, hb11,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, rfl, (fun r hr => ?_), rfl, rfl⟩
  · have doubled : (s.gpr a + s.gpr a).toNat = 2 * (s.gpr a).toNat := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
      omega
    have cap : (s.gpr a + s.gpr a).toNat * (s.gpr b).toNat +
        VG.Proof.X448.Wide.pair (s.gpr .x4) (s.gpr .x5) < 2 ^ 128 := by
      rw [doubled, Nat.mul_assoc]; exact h
    have hv := VG.Proof.X448.Wide.madd128 (s.gpr a + s.gpr a) (s.gpr b) (s.gpr .x4) (s.gpr .x5) cap
    rw [doubled, Nat.mul_assoc] at hv
    dsimp only [addCarry, carryOut, mulHi, Size.bits] at hv ⊢
    exact hv
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr, ite_false]

end VG.Proof.X448.Wide

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Wide.AccumSquareBody`. -/
section

/-! Untrusted: accumulate a square diagonal into an existing coefficient. -/
namespace VG.Proof.X448.Wide
open VG VG.AArch64
open VG.Impl.X448.AArch64.Wide VG.Impl.X448.AArch64.Cached VG.Proof.X448.AArch64
theorem accumSquareBody_ok {s : State} {f : Nat → Nat} {k : Nat} (hk : k < 16)
    (fc : ∀ i < 8, (s.gpr (cacheReg i)).toNat = f i)
    (fb : ∀ i < 8, f i < VG.Proof.X448.Wide.radix) {c : Nat} (hc : c < 2 ^ 118)
    (hz : VG.Proof.X448.Wide.pair (s.gpr .x4) (s.gpr .x5) = c) :
    WP isa (.block (Impl.X448.AArch64.Symmetric.body k)) s fun t =>
      VG.Proof.X448.Wide.pair (t.gpr .x4) (t.gpr .x5) = c + VG.Proof.X448.Wide.rows f f 8 k ∧ t.mem = s.mem ∧ Keeps VG.Proof.X448.Wide.termRegs s t := by
  let inv := fun n (t : State) =>
    VG.Proof.X448.Wide.pair (t.gpr .x4) (t.gpr .x5) = c + VG.Proof.X448.Wide.sqrSum f k n ∧ t.mem = s.mem ∧ Keeps VG.Proof.X448.Wide.termRegs s t
  have step : ∀ n t, n < 8 → inv n t → WP isa (.block (if n ≤ k ∧ k < n + 8 ∧ n ≤ k - n then
      if n = k - n then termFrom (cacheReg n) (cacheReg (k - n))
      else termFromDouble (cacheReg n) (cacheReg (k - n)) else [])) t (inv (n + 1)) := by
    intro n t hn ⟨tv, tm, tk⟩
    by_cases h : n ≤ k ∧ k < n + 8 ∧ n ≤ k - n
    · rw [ite_eq_left h]
      have hj : k - n < 8 := by omega
      have av : (t.gpr (cacheReg n)).toNat = f n := by rw [tk.1 _ (VG.Proof.X448.Wide.cacheReg_kept hn), fc n hn]
      have bv : (t.gpr (cacheReg (k - n))).toNat = f (k - n) := by
        rw [tk.1 _ (VG.Proof.X448.Wide.cacheReg_kept hj), fc (k - n) hj]
      have next := VG.Proof.X448.Wide.sqrSum_bound fb (n := n + 1) (by omega) hk
      by_cases diag : n = k - n
      · rw [ite_eq_left diag]
        have sum : (t.gpr (cacheReg n)).toNat * (t.gpr (cacheReg (k - n))).toNat +
            VG.Proof.X448.Wide.pair (t.gpr .x4) (t.gpr .x5) < 2 ^ 128 := by
          rw [av, bv, tv]
          simp only [VG.Proof.X448.Wide.sqrSum, ite_eq_left h, ite_eq_left diag] at next
          omega
        refine WP.mono (VG.Proof.X448.Wide.termFrom_ok t _ _ (VG.Proof.X448.Wide.cacheReg_ne10 hn) (VG.Proof.X448.Wide.cacheReg_ne10 hj) sum) fun u ⟨uv, um, uk⟩ => ?_
        refine ⟨?_, um.trans tm, tk.trans uk⟩
        rw [uv, av, bv, tv, VG.Proof.X448.Wide.sqrSum, ite_eq_left h, ite_eq_left diag]
        omega
      · rw [ite_eq_right diag]
        have sum : 2 * ((t.gpr (cacheReg n)).toNat * (t.gpr (cacheReg (k - n))).toNat) +
            VG.Proof.X448.Wide.pair (t.gpr .x4) (t.gpr .x5) < 2 ^ 128 := by
          rw [av, bv, tv]
          simp only [VG.Proof.X448.Wide.sqrSum, ite_eq_left h, ite_eq_right diag] at next
          omega
        refine WP.mono (VG.Proof.X448.Wide.termFromDouble_ok t _ _ (VG.Proof.X448.Wide.cacheReg_ne10 hj) (VG.Proof.X448.Wide.cacheReg_ne11 hj)
          (by rw [av]; exact Nat.lt_trans (fb n hn) (by decide : VG.Proof.X448.Wide.radix < 2 ^ 63)) sum) fun u ⟨uv, um, uk⟩ => ?_
        refine ⟨?_, um.trans tm, tk.trans uk⟩
        rw [uv, av, bv, tv, VG.Proof.X448.Wide.sqrSum, ite_eq_left h, ite_eq_right diag]
        omega
    · rw [ite_eq_right h]
      apply WP.block_nil
      exact ⟨by rw [VG.Proof.X448.Wide.sqrSum, ite_eq_right h, Nat.add_zero]; exact tv, tm, tk⟩
  rw [Impl.X448.AArch64.Symmetric.body]
  refine WP.mono (wp_range_flatMap (M := isa) (N := 8) inv step 8 (by decide) s
    ⟨by simpa only [VG.Proof.X448.Wide.sqrSum, Nat.add_zero] using hz, rfl, Keeps.refl _ _⟩) fun t ⟨tv, tm, tk⟩ => ?_
  rw [VG.Proof.X448.Wide.sqrSum_eq f hk] at tv
  exact ⟨tv, tm, tk⟩

end VG.Proof.X448.Wide

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Wide.Columns`. -/
section

/-! Untrusted: the complete two-word coefficient array of a wide product. -/
namespace VG.Proof.X448.Wide

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ACC)
open VG.Impl.X448.AArch64.Wide VG.Proof.X448.AArch64

theorem columns_ok {s : State} {base : Addr} (hs : Scr s base) {a b : Nat}
    (ha : a + 64 ≤ ACC ∨ ACC + 256 ≤ a) (hb : b + 64 ≤ ACC ∨ ACC + 256 ≤ b)
    (ha' : a + 64 ≤ 8192) (hb' : b + 64 ≤ 8192) (ha8 : a % 8 = 0) (hb8 : b % 8 = 0)
    (fa : ∀ i < 8, limbs s.mem base a i < VG.Proof.X448.Wide.radix)
    (fb : ∀ i < 8, limbs s.mem base b i < VG.Proof.X448.Wide.radix) :
    WP isa (.block ((List.range 16).flatMap (column a b))) s fun t =>
      (∀ k < 16, VG.Proof.X448.Wide.coeff t.mem base ACC k = VG.Proof.X448.Wide.rows (limbs s.mem base a) (limbs s.mem base b) 8 k) ∧
      Outside base ACC 256 s.mem t.mem ∧ Keeps VG.Proof.X448.Wide.colRegs s t := by
  let f := limbs s.mem base a
  let g := limbs s.mem base b
  let inv := fun n (t : State) =>
    (∀ k < 16, VG.Proof.X448.Wide.coeff t.mem base ACC k = if k < n then VG.Proof.X448.Wide.rows f g 8 k else VG.Proof.X448.Wide.coeff s.mem base ACC k) ∧
    Outside base ACC 256 s.mem t.mem ∧ Keeps VG.Proof.X448.Wide.colRegs s t
  have step : ∀ n t, n < 16 → inv n t → WP isa (.block (column a b n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    have av : ∀ i < 8, limbs t.mem base a i = f i := by
      intro i hi
      exact congrArg BitVec.toNat (tm.word (by omega) (by omega))
    have bv : ∀ i < 8, limbs t.mem base b i = g i := by
      intro i hi
      exact congrArg BitVec.toNat (tm.word (by omega) (by omega))
    refine WP.mono (VG.Proof.X448.Wide.column_ok (hs.of_keeps tk (by decide)) ha' hb' ha8 hb8 hn
      (by intro i hi; rw [av i hi]; exact fa i hi)
      (by intro i hi; rw [bv i hi]; exact fb i hi)) fun u ⟨uv, um, uk⟩ => ?_
    refine ⟨?_, tm.trans (um.mono (by omega) (by omega)), tk.trans uk⟩
    intro k hk
    by_cases h : k = n
    · subst k
      rw [ite_eq_left (by omega), uv]
      exact VG.Proof.X448.Wide.rows_congr av bv (by decide) n
    · have hsep : ACC + 16 * k + 16 ≤ ACC + 16 * n ∨
          ACC + 16 * n + 16 ≤ ACC + 16 * k := by omega
      change VG.Proof.X448.Wide.pair (word u.mem base (ACC + 16 * k)) (word u.mem base (ACC + 16 * k + 8)) = _
      rw [VG.Proof.X448.Wide.outside_coeff um hsep (by simp only [ACC]; omega)]
      change VG.Proof.X448.Wide.coeff t.mem base ACC k = _
      rw [tf k hk]
      have e : (k < n) = (k < n + 1) := propext (by omega)
      simp only [e]
  have init : inv 0 s := ⟨by intro k _; rw [ite_eq_right (by omega)], Outside.refl _ _ _ _, Keeps.refl _ _⟩
  refine WP.mono (wp_range_flatMap (M := isa) (N := 16) inv step 16 (by decide) s init)
    fun t ⟨tf, tm, tk⟩ => ?_
  exact ⟨fun k hk => (tf k hk).trans (ite_eq_left hk), tm, tk⟩

end VG.Proof.X448.Wide

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Wide.Bridge`. -/
section

/-! Untrusted: the exact-value bridge between the old and wide limb layouts. -/
namespace VG.Proof.X448.Wide

/-- Combine two neighboring 28-bit limbs. -/
def paired (f : Nat → Nat) (i : Nat) : Nat :=
  f (2 * i) + VG.Proof.X448.radix * f (2 * i + 1)

theorem radix_pair : VG.Proof.X448.radix ^ 2 = VG.Proof.X448.Wide.radix := by decide

theorem paired_val (f : Nat → Nat) (n : Nat) :
    VG.Proof.X448.Wide.valN (VG.Proof.X448.Wide.paired f) n = VG.Proof.X448.valN f (2 * n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
      VG.Proof.X448.valN_succ, VG.Proof.X448.valN_succ, VG.Proof.X448.Wide.valN_succ, ih, VG.Proof.X448.Wide.paired,
      Nat.pow_succ, Nat.pow_mul, VG.Proof.X448.Wide.radix_pair, Nat.mul_add, Nat.add_assoc, Nat.mul_assoc]

theorem paired_bound {f : Nat → Nat} (h : ∀ i < 16, f i < VG.Proof.X448.radix) :
    ∀ i < 8, VG.Proof.X448.Wide.paired f i < VG.Proof.X448.Wide.radix := by
  intro i hi
  have h0 := h (2 * i) (by omega)
  have h1 := h (2 * i + 1) (by omega)
  simp only [VG.Proof.X448.Wide.paired, VG.Proof.X448.radix, VG.Proof.X448.Wide.radix] at *
  omega

/-- Split a normalized wide limb back into the existing field-slot layout. -/
def unpacked (f : Nat → Nat) (i : Nat) : Nat :=
  if i % 2 = 0 then f (i / 2) % VG.Proof.X448.radix else f (i / 2) / VG.Proof.X448.radix

theorem paired_unpacked (f : Nat → Nat) (i : Nat) : VG.Proof.X448.Wide.paired (VG.Proof.X448.Wide.unpacked f) i = f i := by
  simp only [VG.Proof.X448.Wide.paired, VG.Proof.X448.Wide.unpacked, show (2 * i) % 2 = 0 by omega,
    show (2 * i + 1) % 2 = 1 by omega, show (2 * i) / 2 = i by omega,
    show (2 * i + 1) / 2 = i by omega, ite_true, ite_false, Nat.one_ne_zero]
  exact Nat.mod_add_div _ _

theorem unpacked_val (f : Nat → Nat) :
    VG.Proof.X448.valN (VG.Proof.X448.Wide.unpacked f) 16 = VG.Proof.X448.Wide.valN f 8 := by
  rw [← VG.Proof.X448.Wide.paired_val (VG.Proof.X448.Wide.unpacked f) 8]
  exact VG.Proof.X448.Wide.valN_congr (fun i _ => VG.Proof.X448.Wide.paired_unpacked f i)

theorem unpacked_bound {f : Nat → Nat} (h : ∀ i < 8, f i < VG.Proof.X448.Wide.radix) :
    ∀ i < 16, VG.Proof.X448.Wide.unpacked f i < VG.Proof.X448.radix := by
  intro i hi
  have hf := h (i / 2) (by omega)
  simp only [VG.Proof.X448.Wide.unpacked]
  split
  · exact Nat.mod_lt _ (by decide)
  · simp only [VG.Proof.X448.Wide.radix] at hf
    simp only [VG.Proof.X448.radix]
    omega

end VG.Proof.X448.Wide

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Wide.Pack`. -/
section

/-! Untrusted: staging normalized 28-bit field slots for the wide kernel. -/
namespace VG.Proof.X448.Wide

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld st)
open VG.Impl.X448.AArch64.Wide VG.Proof.X448.AArch64

theorem pack_word (lo hi : BitVec 64) (hl : lo.toNat < VG.Proof.X448.radix)
    (hh : hi.toNat < VG.Proof.X448.radix) :
    (lo + (hi <<< 28)).toNat = lo.toNat + VG.Proof.X448.radix * hi.toNat := by
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  simp only [VG.Proof.X448.radix] at hl hh ⊢
  have hb : hi.toNat * 2 ^ 28 < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt (by omega)]
  omega

theorem packStep_ok {s : State} {base : Addr} (hs : Scr s base) {o a i : Nat}
    (ho : o + 64 ≤ 8192) (ha : a + 128 ≤ 8192)
    (ho8 : o % 8 = 0) (ha8 : a % 8 = 0) (hi : i < 8)
    (hb : Bounded s.mem base a) :
    WP isa (.block (packStep o a i)) s fun t =>
      t.mem = s.mem.writeW (off base (o + 8 * i))
        (BitVec.ofNat 64 (VG.Proof.X448.Wide.paired (limbs s.mem base a) i)) ∧ Keeps [.x4, .x5] s t := by
  have al := hs.read (d := a + 16 * i) (n := 8) (by omega)
  have bl := hs.read (d := a + 16 * i + 8) (n := 8) (by omega)
  have ow := hs.write (d := o + 8 * i) (n := 8) (by omega)
  have ae : (a + 16 * i) % 8 = 0 ∧ a + 16 * i < 32768 := ⟨by omega, by omega⟩
  have be : (a + 16 * i + 8) % 8 = 0 ∧ a + 16 * i + 8 < 32768 := ⟨by omega, by omega⟩
  have oe : (o + 8 * i) % 8 = 0 ∧ o + 8 * i < 32768 := ⟨by omega, by omega⟩
  have e0 : a + 8 * (2 * i) = a + 16 * i := by omega
  have e1 : a + 8 * (2 * i + 1) = a + 16 * i + 8 := by omega
  apply WP.of_runBlock
  simp only [packStep, ld, st, runBlock_cons, runStep_some, runBlock_nil, exec, addr,
    Size.bytes, Size.bits, ae, be, oe, and_self, State.read, State.load, State.store,
    hs.x3, al, bl, ow, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, Nat.reduceLT,
    Option.map_some, Option.bind_some, read8_eq, write8_eq,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, (fun r hr => ?_), rfl, rfl⟩
  · apply congrArg (s.mem.writeW (off base (o + 8 * i)))
    apply BitVec.eq_of_toNat_eq
    have h0 : (word s.mem base (a + 16 * i)).toNat < VG.Proof.X448.radix := by
      simpa only [limbs, e0] using hb (2 * i) (by omega)
    have h1 : (word s.mem base (a + 16 * i + 8)).toNat < VG.Proof.X448.radix := by
      simpa only [limbs, e1] using hb (2 * i + 1) (by omega)
    rw [VG.Proof.X448.Wide.pack_word _ _ h0 h1, BitVec.toNat_ofNat]
    have cap := VG.Proof.X448.Wide.paired_bound hb i hi
    rw [Nat.mod_eq_of_lt (Nat.lt_trans cap (show VG.Proof.X448.Wide.radix < 2 ^ 64 by decide))]
    simp only [VG.Proof.X448.Wide.paired, limbs, e0, e1]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr, ite_false]

theorem pack_ok {s : State} {base : Addr} (hs : Scr s base) {o a : Nat}
    (ho : o + 64 ≤ 8192) (ha : a + 128 ≤ 8192)
    (ho8 : o % 8 = 0) (ha8 : a % 8 = 0)
    (hsep : a + 128 ≤ o ∨ o + 64 ≤ a) (hb : Bounded s.mem base a) :
    WP isa (.block (pack o a)) s fun t =>
      (∀ i < 8, limbs t.mem base o i = VG.Proof.X448.Wide.paired (limbs s.mem base a) i) ∧
      Outside base o 64 s.mem t.mem ∧ Keeps [.x4, .x5] s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, limbs t.mem base o i = VG.Proof.X448.Wide.paired (limbs s.mem base a) i) ∧
    Outside base o 64 s.mem t.mem ∧ Keeps [.x4, .x5] s t
  have step : ∀ n t, n < 8 → inv n t → WP isa (.block (packStep o a n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    have av : ∀ i < 16, limbs t.mem base a i = limbs s.mem base a i :=
      fun i hi => tm.limbs (by omega) ha hi
    have tb : Bounded t.mem base a := by
      intro i hi
      rw [av i hi]
      exact hb i hi
    refine WP.mono (VG.Proof.X448.Wide.packStep_ok (hs.of_keeps tk (by decide)) ho ha ho8 ha8 hn tb)
      fun u ⟨um, uk⟩ => ?_
    have out : Outside base (o + 8 * n) 8 t.mem u.mem := by
      rw [um]
      exact writeW_outside _ _ _ (by omega)
    refine ⟨?_, tm.trans (out.mono (by omega) (by omega)), tk.trans uk⟩
    intro i hi
    change (word u.mem base (o + 8 * i)).toNat = _
    rw [um, word_write _ base (by omega) (by omega)]
    by_cases h : i = n
    · subst i
      rw [ite_eq_left rfl, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (Nat.lt_trans (VG.Proof.X448.Wide.paired_bound tb n hn) (show VG.Proof.X448.Wide.radix < 2 ^ 64 by decide))]
      simp only [VG.Proof.X448.Wide.paired]
      rw [av (2 * n) (by omega), av (2 * n + 1) (by omega)]
    · rw [ite_eq_right h]
      exact tf i (by omega)
  exact wp_range_flatMap (M := isa) (N := 8) inv step 8 (by decide) s
    ⟨fun _ hi => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩

end VG.Proof.X448.Wide

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Wide.AddCoefficient`. -/
section

/-! Untrusted: wide coefficient addition for reduction modulo the X448 prime. -/
namespace VG.Proof.X448.Wide

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld st ACC TMP)
open VG.Impl.X448.AArch64.Wide VG.Proof.X448.AArch64 VG.Proof.Ed25519.Word64
open VG.Proof.Ed25519.AArch64 (read_x)

theorem addRegs_ok (s : State)
    (h : VG.Proof.X448.Wide.pair (s.gpr .x4) (s.gpr .x5) + VG.Proof.X448.Wide.pair (s.gpr .x6) (s.gpr .x9) < 2 ^ 128) :
    WP isa (.block [.adds .x .x4 .x4 .x6, .adcs .x .x5 .x5 .x9]) s fun t =>
      VG.Proof.X448.Wide.pair (t.gpr .x4) (t.gpr .x5) =
        VG.Proof.X448.Wide.pair (s.gpr .x4) (s.gpr .x5) + VG.Proof.X448.Wide.pair (s.gpr .x6) (s.gpr .x9) ∧
      t.mem = s.mem ∧ Keeps [.x4, .x5] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry,
    BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, rfl, (fun r hr => ?_), rfl, rfl⟩
  · have hv := VG.Proof.X448.Wide.addPair128 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x9) h
    dsimp only [addCarry, carryOut, Size.bits] at hv ⊢
    exact hv
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_addWithCarry, hr, ite_false]

theorem addCoeff_ok {s : State} {base : Addr} (hs : Scr s base) {i : Nat} (hi : i < 16)
    (h : VG.Proof.X448.Wide.pair (s.gpr .x4) (s.gpr .x5) + VG.Proof.X448.Wide.coeff s.mem base ACC i < 2 ^ 128) :
    WP isa (.block (addCoeff i)) s fun t =>
      VG.Proof.X448.Wide.pair (t.gpr .x4) (t.gpr .x5) = VG.Proof.X448.Wide.pair (s.gpr .x4) (s.gpr .x5) + VG.Proof.X448.Wide.coeff s.mem base ACC i ∧
      t.mem = s.mem ∧ Keeps VG.Proof.X448.Wide.colRegs s t := by
  rw [show addCoeff i = [ld .x6 (ACC + 16 * i), ld .x9 (ACC + 16 * i + 8)] ++
    [.adds .x .x4 .x4 .x6, .adcs .x .x5 .x5 .x9] from rfl, WP.block_append_iff]
  have load := VG.Proof.X448.Wide.loadTerm_ok hs (a := ACC + 16 * i) (b := ACC + 16 * i + 8)
    (i := 0) (j := 0) (by simp only [ACC]; omega) (by simp only [ACC]; omega)
    (by simp only [ACC]; omega) (by simp only [ACC]; omega) (by decide) (by decide)
  simp only [Nat.mul_zero, Nat.add_zero] at load
  refine WP.mono load fun u ⟨u6, u9, um, uk⟩ => ?_
  have uv : VG.Proof.X448.Wide.pair (u.gpr .x4) (u.gpr .x5) = VG.Proof.X448.Wide.pair (s.gpr .x4) (s.gpr .x5) := by
    rw [uk.1 .x4 (by decide), uk.1 .x5 (by decide)]
  have up : VG.Proof.X448.Wide.pair (u.gpr .x6) (u.gpr .x9) = VG.Proof.X448.Wide.coeff s.mem base ACC i := by rw [u6, u9]
  refine WP.mono (VG.Proof.X448.Wide.addRegs_ok u (by rw [uv, up]; exact h)) fun t ⟨tv, tm, tk⟩ => ?_
  exact ⟨by rw [tv, uv, up], tm.trans um, (uk.mono (by decide)).trans (tk.mono (by decide))⟩

theorem addCoeffs_ok {s : State} {base : Addr} (hs : Scr s base) (xs : List Nat)
    (hx : ∀ i ∈ xs, i < 16)
    (h : VG.Proof.X448.Wide.pair (s.gpr .x4) (s.gpr .x5) + (xs.map (VG.Proof.X448.Wide.coeff s.mem base ACC)).sum < 2 ^ 128) :
    WP isa (.block (xs.flatMap addCoeff)) s fun t =>
      VG.Proof.X448.Wide.pair (t.gpr .x4) (t.gpr .x5) =
        VG.Proof.X448.Wide.pair (s.gpr .x4) (s.gpr .x5) + (xs.map (VG.Proof.X448.Wide.coeff s.mem base ACC)).sum ∧
      t.mem = s.mem ∧ Keeps VG.Proof.X448.Wide.colRegs s t := by
  induction xs generalizing s with
  | nil =>
    simp only [List.flatMap_nil, List.map_nil, List.sum_nil, Nat.add_zero]
    exact WP.block_nil ⟨rfl, rfl, Keeps.refl _ _⟩
  | cons i xs ih =>
    rw [List.flatMap_cons, WP.block_append_iff]
    have hi := hx i List.mem_cons_self
    have hc : VG.Proof.X448.Wide.pair (s.gpr .x4) (s.gpr .x5) + VG.Proof.X448.Wide.coeff s.mem base ACC i < 2 ^ 128 := by
      simp only [List.map_cons, List.sum_cons] at h
      omega
    refine WP.mono (VG.Proof.X448.Wide.addCoeff_ok hs hi hc) fun u ⟨uv, um, uk⟩ => ?_
    refine WP.mono (ih (hs.of_keeps uk (by decide))
      (fun j hj => hx j (List.mem_cons_of_mem _ hj)) (by
        rw [uv, um]
        simpa only [List.map_cons, List.sum_cons, Nat.add_assoc] using h)) fun t ⟨tv, tm, tk⟩ => ?_
    refine ⟨?_, tm.trans um, uk.trans tk⟩
    rw [tv, uv, um]
    simp only [List.map_cons, List.sum_cons, Nat.add_assoc]

end VG.Proof.X448.Wide

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Wide.CoefficientIO`. -/
section

/-! Untrusted: coefficient reads and writes inside the X448 scratch buffer. -/
namespace VG.Proof.X448.Wide

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld st)
open VG.Proof.X448.AArch64

theorem loadAt_ok {s : State} {base : Addr} (hs : Scr s base) {o k : Nat}
    (ho : o + 16 * k + 16 ≤ 8192) (ho8 : o % 8 = 0) :
    WP isa (.block [ld .x4 (o + 16 * k), ld .x5 (o + 16 * k + 8)]) s fun t =>
      VG.Proof.X448.Wide.pair (t.gpr .x4) (t.gpr .x5) = VG.Proof.X448.Wide.coeff s.mem base o k ∧
      t.mem = s.mem ∧ Keeps [.x4, .x5] s t := by
  have ae : (o + 16 * k) % 8 = 0 ∧ o + 16 * k < 32768 := ⟨by omega, by omega⟩
  have be : (o + 16 * k + 8) % 8 = 0 ∧ o + 16 * k + 8 < 32768 := ⟨by omega, by omega⟩
  have al := hs.read (d := o + 16 * k) (n := 8) (by omega)
  have bl := hs.read (d := o + 16 * k + 8) (n := 8) (by omega)
  apply WP.of_runBlock
  simp only [ld, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
    ae, be, and_self, State.load, hs.x3, al, bl, ite_true, Option.map_some,
    Option.bind_some, BitVec.setWidth_eq, read8_eq, RegUpd.gpr_write,
    ite_false, reduceCtorEq, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

theorem storeAt_ok {s : State} {base : Addr} (hs : Scr s base) {o k : Nat}
    (ho : o + 16 * k + 16 ≤ 8192) (ho8 : o % 8 = 0)
    (r0 : Reg := .x4) (r1 : Reg := .x5) :
    WP isa (.block [st r0 (o + 16 * k), st r1 (o + 16 * k + 8)]) s fun t =>
      t.mem = VG.Proof.X448.Wide.putCoeff s.mem base o k (s.gpr r0) (s.gpr r1) ∧ Keeps [] s t := by
  have ae : (o + 16 * k) % 8 = 0 ∧ o + 16 * k < 32768 := ⟨by omega, by omega⟩
  have be : (o + 16 * k + 8) % 8 = 0 ∧ o + 16 * k + 8 < 32768 := ⟨by omega, by omega⟩
  have aw := hs.write (d := o + 16 * k) (n := 8) (by omega)
  have bw := hs.write (d := o + 16 * k + 8) (n := 8) (by omega)
  apply WP.of_runBlock
  simp only [st, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
    ae, be, and_self, State.read, State.store, hs.x3, aw, bw, ite_true,
    Option.bind_some, BitVec.setWidth_eq, write8_eq, Option.some.injEq, exists_eq_left']
  exact ⟨rfl, (fun _ _ => rfl), rfl, rfl⟩

end VG.Proof.X448.Wide

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Wide.Reduce`. -/
section

/-! Untrusted: fold wide product coefficients with 2⁴⁴⁸ = 2²²⁴ + 1. -/
namespace VG.Proof.X448.Wide

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld st ACC TMP)
open VG.Impl.X448.AArch64.Wide VG.Proof.X448.AArch64

theorem reduction_sum (f : Nat → Nat) (k : Nat) :
    f k + ((reduceIndices k).map f).sum = VG.Proof.X448.Wide.reduced f k := by
  by_cases hk : k < 4
  · simp only [reduceIndices, hk, ite_true, List.singleton_append,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, VG.Proof.X448.Wide.reduced, Nat.add_assoc]
  · simp only [reduceIndices, hk, ite_false, List.singleton_append,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, VG.Proof.X448.Wide.reduced,
      Nat.add_assoc]

theorem reduceCol_ok {s : State} {base : Addr} (hs : Scr s base) {k : Nat} (hk : k < 8)
    (hb : ∀ i < 16, VG.Proof.X448.Wide.coeff s.mem base ACC i < 2 ^ 116) :
    WP isa (.block (reduceCol k)) s fun t =>
      VG.Proof.X448.Wide.coeff t.mem base TMP k = VG.Proof.X448.Wide.reduced (VG.Proof.X448.Wide.coeff s.mem base ACC) k ∧
      Outside base (TMP + 16 * k) 16 s.mem t.mem ∧ Keeps VG.Proof.X448.Wide.colRegs s t := by
  rw [reduceCol, List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Wide.loadAt_ok hs (o := ACC) (k := k) (by simp only [ACC]; omega) (by decide))
    fun u ⟨uv, um, uk⟩ => ?_
  rw [WP.block_append_iff]
  have ids : ∀ i ∈ reduceIndices k, i < 16 := by
    intro i hi
    by_cases h : k < 4 <;> simp only [reduceIndices, h, ite_true, ite_false,
      List.singleton_append, List.mem_cons, List.not_mem_nil, or_false] at hi <;>
      rcases hi with rfl | rfl | rfl <;> omega
  have cap : VG.Proof.X448.Wide.pair (u.gpr .x4) (u.gpr .x5) +
      ((reduceIndices k).map (VG.Proof.X448.Wide.coeff u.mem base ACC)).sum < 2 ^ 128 := by
    rw [uv, um, VG.Proof.X448.Wide.reduction_sum]
    exact Nat.lt_trans (VG.Proof.X448.Wide.reduced_bound hb k hk) (by decide)
  refine WP.mono (VG.Proof.X448.Wide.addCoeffs_ok (hs.of_keeps uk (by decide)) (reduceIndices k) ids cap)
    fun v ⟨vv, vm, vk⟩ => ?_
  have vs := (hs.of_keeps uk (by decide)).of_keeps vk (by decide)
  refine WP.mono (VG.Proof.X448.Wide.storeAt_ok vs (o := TMP) (k := k) (by simp only [TMP]; omega) (by decide))
    fun t ⟨tm, tk⟩ => ?_
  refine ⟨?_, ?_, (uk.mono (by decide)).trans (vk.trans (tk.mono (by decide)))⟩
  · rw [tm, VG.Proof.X448.Wide.coeff_put _ base _ _ (by simp only [TMP]; omega)
      (by simp only [TMP]; omega), ite_eq_left rfl, vv, uv, um, VG.Proof.X448.Wide.reduction_sum]
  · rw [tm, vm, um]
    exact VG.Proof.X448.Wide.putCoeff_outside _ _ _ _ (by simp only [TMP]; omega)

theorem reduce_ok {s : State} {base : Addr} (hs : Scr s base)
    (hb : ∀ i < 16, VG.Proof.X448.Wide.coeff s.mem base ACC i < 2 ^ 116) :
    WP isa (.block ((List.range 8).flatMap reduceCol)) s fun t =>
      (∀ k < 8, VG.Proof.X448.Wide.coeff t.mem base TMP k = VG.Proof.X448.Wide.reduced (VG.Proof.X448.Wide.coeff s.mem base ACC) k) ∧
      Outside base TMP 128 s.mem t.mem ∧ Keeps VG.Proof.X448.Wide.colRegs s t := by
  let f := VG.Proof.X448.Wide.coeff s.mem base ACC
  let inv := fun n (t : State) =>
    (∀ k < n, VG.Proof.X448.Wide.coeff t.mem base TMP k = VG.Proof.X448.Wide.reduced f k) ∧
    Outside base TMP 128 s.mem t.mem ∧ Keeps VG.Proof.X448.Wide.colRegs s t
  have step : ∀ n t, n < 8 → inv n t → WP isa (.block (reduceCol n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    have av : ∀ i < 16, VG.Proof.X448.Wide.coeff t.mem base ACC i = f i := by
      intro i hi
      exact VG.Proof.X448.Wide.outside_coeff tm (by simp only [ACC, TMP]; omega) (by simp only [ACC]; omega)
    have tb : ∀ i < 16, VG.Proof.X448.Wide.coeff t.mem base ACC i < 2 ^ 116 := by
      intro i hi
      rw [av i hi]
      exact hb i hi
    refine WP.mono (VG.Proof.X448.Wide.reduceCol_ok (hs.of_keeps tk (by decide)) hn tb) fun u ⟨uv, um, uk⟩ => ?_
    refine ⟨?_, tm.trans (um.mono (by omega) (by omega)), tk.trans uk⟩
    intro k hk
    by_cases h : k = n
    · subst k
      rw [uv]
      simp only [VG.Proof.X448.Wide.reduced]
      rw [av n (by omega), av (n + 8) (by omega)]
      split
      · rename_i hn'
        rw [av (n + 12) (by omega)]
      · rw [av (n + 4) (by omega)]
    · change VG.Proof.X448.Wide.pair (word u.mem base (TMP + 16 * k)) (word u.mem base (TMP + 16 * k + 8)) = _
      rw [VG.Proof.X448.Wide.outside_coeff um (by omega) (by simp only [TMP]; omega)]
      exact tf k (by omega)
  exact wp_range_flatMap (M := isa) (N := 8) inv step 8 (by decide) s
    ⟨fun _ hi => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩

end VG.Proof.X448.Wide

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Wide.CarryRegs`. -/
section

/-! Untrusted: extracting a radix-2⁵⁶ digit and one-word carry. -/
namespace VG.Proof.X448.Wide

open VG VG.AArch64
open VG.Impl.X448.AArch64.Wide VG.Proof.X448.AArch64 VG.Proof.Ed25519.Word64
open VG.Proof.Ed25519.AArch64 (read_x)

theorem carryRegs_ok (s : State) (hz : s.gpr .x11 = 0)
    (hm : s.gpr .x9 = BitVec.ofNat 64 (2 ^ 56 - 1))
    (hb : VG.Proof.X448.Wide.pair (s.gpr .x4) (s.gpr .x5) + (s.gpr .x6).toNat < 2 ^ 119) :
    let v := VG.Proof.X448.Wide.pair (s.gpr .x4) (s.gpr .x5) + (s.gpr .x6).toNat
    WP isa (.block carryRegs) s fun t =>
      (t.gpr .x4).toNat = v % VG.Proof.X448.Wide.radix ∧ (t.gpr .x6).toNat = v / VG.Proof.X448.Wide.radix ∧
      t.mem = s.mem ∧ Keeps [.x4, .x5, .x6] s t := by
  intro v
  let lo := addCarry (s.gpr .x4) (s.gpr .x6) false
  let hi := addCarry (s.gpr .x5) 0 (carryOut (s.gpr .x4) (s.gpr .x6) false)
  have hv : VG.Proof.X448.Wide.pair lo hi = v := VG.Proof.X448.Wide.add128 _ _ _ (Nat.lt_trans hb (by decide))
  have hd := VG.Proof.X448.Wide.low56 lo hi
  have hc := VG.Proof.X448.Wide.high56 lo hi (by rw [hv]; exact hb)
  rw [hv] at hd hc
  apply WP.of_runBlock
  simp only [carryRegs, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry,
    BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, hz, hm,
    show 56 < Size.x.bits from by decide, show 8 < Size.x.bits from by decide,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, rfl, (fun r hr => ?_), rfl, rfl⟩
  · dsimp only [lo, hi, addCarry, carryOut, Size.bits] at hd ⊢
    exact hd
  · dsimp only [lo, hi, addCarry, carryOut, Size.bits] at hc ⊢
    exact hc
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr, ite_false]

end VG.Proof.X448.Wide

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Wide.UnpackRegs`. -/
section

/-! Untrusted: split a wide digit into two normalized interface limbs. -/
namespace VG.Proof.X448.Wide

open VG VG.AArch64 VG.Proof.X448.AArch64

theorem unpackRegs_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block [.lsr .x .x5 .x4 28, .logic .and .x .x4 .x4 .x12]) s fun t =>
      (t.gpr .x4).toNat = (s.gpr .x4).toNat % VG.Proof.X448.radix ∧
      (t.gpr .x5).toNat = (s.gpr .x4).toNat / VG.Proof.X448.radix ∧
      t.mem = s.mem ∧ Keeps [.x4, .x5] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    Nat.reduceLT, RegUpd.gpr_write, BitVec.setWidth_eq, ite_true, ite_false,
    reduceCtorEq, hs.mask, Option.some.injEq, exists_eq_left']
  refine ⟨and28 _, shr28 _, rfl, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

end VG.Proof.X448.Wide

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Wide.CarryStep`. -/
section

/-! Untrusted: one wide carry step and its optional interface conversion. -/
namespace VG.Proof.X448.Wide

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld st TMP)
open VG.Impl.X448.AArch64.Wide VG.Proof.X448.AArch64

def encoded (v : Nat) (unpack : Bool) : Nat :=
  if unpack then v % VG.Proof.X448.radix + 2 ^ 64 * (v / VG.Proof.X448.radix) else v

theorem carryStep_ok {s : State} {base : Addr} (hs : Scr s base) {o i : Nat}
    (ho : o + 128 ≤ 8192) (ho8 : o % 8 = 0) (hi : i < 8) (unpack : Bool)
    (hz : s.gpr .x11 = 0) (hm : s.gpr .x9 = BitVec.ofNat 64 (2 ^ 56 - 1))
    (hb : VG.Proof.X448.Wide.coeff s.mem base TMP i + (s.gpr .x6).toNat < 2 ^ 119) :
    let v := VG.Proof.X448.Wide.coeff s.mem base TMP i + (s.gpr .x6).toNat
    WP isa (.block (carryStep o i unpack)) s fun t =>
      (t.gpr .x6).toNat = v / VG.Proof.X448.Wide.radix ∧ VG.Proof.X448.Wide.coeff t.mem base o i = VG.Proof.X448.Wide.encoded (v % VG.Proof.X448.Wide.radix) unpack ∧
      Outside base (o + 16 * i) 16 s.mem t.mem ∧ Keeps [.x4, .x5, .x6] s t := by
  intro v
  rw [carryStep, List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Wide.loadAt_ok hs (o := TMP) (k := i) (by simp only [TMP]; omega) (by decide))
    fun u ⟨uv, um, uk⟩ => ?_
  rw [WP.block_append_iff]
  have uz : u.gpr .x11 = 0 := (uk.1 _ (by decide)).trans hz
  have u9 : u.gpr .x9 = BitVec.ofNat 64 (2 ^ 56 - 1) := (uk.1 _ (by decide)).trans hm
  have raw : VG.Proof.X448.Wide.pair (u.gpr .x4) (u.gpr .x5) + (u.gpr .x6).toNat = v := by
    rw [uv, uk.1 .x6 (by decide)]
  refine WP.mono (VG.Proof.X448.Wide.carryRegs_ok u uz u9 (by rw [raw]; exact hb)) fun w ⟨w4, w6, wm, wk⟩ => ?_
  rw [raw] at w4 w6
  have ws := (hs.of_keeps uk (by decide)).of_keeps wk (by decide)
  have wkeep : Keeps [.x4, .x5, .x6] s w := (uk.mono (by decide)).trans (wk.mono (by decide))
  cases unpack with
  | false =>
    rw [ite_eq_right (by decide)]
    refine WP.mono (VG.Proof.X448.Wide.storeAt_ok ws (k := i) (by omega) ho8 .x4 .x11) fun t ⟨tm, tk⟩ => ?_
    have wz : w.gpr .x11 = 0 := (wk.1 _ (by decide)).trans uz
    refine ⟨?_, ?_, ?_, wkeep.trans (tk.mono (by decide))⟩
    · rw [tk.1 .x6 (by decide)]; exact w6
    · rw [tm, VG.Proof.X448.Wide.coeff_put _ base _ _ (by omega) (by omega), ite_eq_left rfl, wz]
      simp only [VG.Proof.X448.Wide.pair, show (0 : BitVec 64).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero,
        VG.Proof.X448.Wide.encoded, Bool.false_eq_true, ite_false]
      exact w4
    · rw [tm, wm, um]
      exact VG.Proof.X448.Wide.putCoeff_outside _ _ _ _ (by omega)
  | true =>
    rw [ite_eq_left (by decide), show
      [.lsr .x .x5 .x4 28, .logic .and .x .x4 .x4 .x12, st .x4 (o + 16 * i), st .x5 (o + 16 * i + 8)] =
      [.lsr .x .x5 .x4 28, .logic .and .x .x4 .x4 .x12] ++
        [st .x4 (o + 16 * i), st .x5 (o + 16 * i + 8)] from rfl, WP.block_append_iff]
    refine WP.mono (VG.Proof.X448.Wide.unpackRegs_ok ws) fun z ⟨z4, z5, zm, zk⟩ => ?_
    have zs := ws.of_keeps zk (by decide)
    refine WP.mono (VG.Proof.X448.Wide.storeAt_ok zs (k := i) (by omega) ho8) fun t ⟨tm, tk⟩ => ?_
    refine ⟨?_, ?_, ?_, wkeep.trans ((zk.mono (by decide)).trans (tk.mono (by decide)))⟩
    · rw [tk.1 .x6 (by decide), zk.1 .x6 (by decide)]; exact w6
    · rw [tm, VG.Proof.X448.Wide.coeff_put _ base _ _ (by omega) (by omega), ite_eq_left rfl]
      simp only [VG.Proof.X448.Wide.pair, VG.Proof.X448.Wide.encoded, ite_true]
      rw [z4, z5, w4]
    · rw [tm, zm, wm, um]
      exact VG.Proof.X448.Wide.putCoeff_outside _ _ _ _ (by omega)

end VG.Proof.X448.Wide

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Wide.PassInit`. -/
section

/-! Untrusted: initialize the carry, zero register, and 56-bit mask. -/
namespace VG.Proof.X448.Wide

open VG VG.AArch64
open VG.Impl.X448.AArch64.Wide VG.Proof.X448.AArch64

theorem passInit_ok (s : State) :
    WP isa (.block passInit) s fun t =>
      t.gpr .x6 = 0 ∧ t.gpr .x11 = 0 ∧ t.gpr .x9 = BitVec.ofNat 64 (2 ^ 56 - 1) ∧
      t.mem = s.mem ∧ Keeps VG.Proof.X448.Wide.colRegs s t := by
  apply WP.of_runBlock
  simp only [passInit, runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    Size.bits, Nat.reduceMul, Nat.reduceLT, ite_true, RegUpd.gpr_write, BitVec.setWidth_eq,
    ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, ?_, rfl, (fun r hr => ?_), rfl, rfl⟩
  · decide
  · simp only [VG.Proof.X448.Wide.colRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr, ite_false]

end VG.Proof.X448.Wide

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Wide.Pass`. -/
section

/-! Untrusted: in-place or disjoint wide carry propagation. -/
namespace VG.Proof.X448.Wide

open VG VG.AArch64
open VG.Impl.X448.AArch64 (TMP)
open VG.Impl.X448.AArch64.Wide VG.Proof.X448.AArch64

theorem pass_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat}
    (ho : o + 128 ≤ 8192) (ho8 : o % 8 = 0)
    (hsep : o = TMP ∨ o + 128 ≤ TMP ∨ TMP + 128 ≤ o) (unpack : Bool)
    {f : Nat → Nat} (hf : ∀ i < 8, VG.Proof.X448.Wide.coeff s.mem base TMP i = f i)
    (hb : ∀ i < 8, f i < 2 ^ 118) :
    WP isa (.block (pass o unpack)) s fun t =>
      (∀ i < 8, VG.Proof.X448.Wide.coeff t.mem base o i = VG.Proof.X448.Wide.encoded (VG.Proof.X448.Wide.digit f i) unpack) ∧
      (t.gpr .x6).toNat = VG.Proof.X448.Wide.carry f 8 ∧ Outside base o 128 s.mem t.mem ∧ Keeps VG.Proof.X448.Wide.colRegs s t := by
  let inv := fun k (t : State) =>
    (∀ i < k, VG.Proof.X448.Wide.coeff t.mem base o i = VG.Proof.X448.Wide.encoded (VG.Proof.X448.Wide.digit f i) unpack) ∧
    (∀ i, k ≤ i → i < 8 → VG.Proof.X448.Wide.coeff t.mem base TMP i = f i) ∧
    (t.gpr .x6).toNat = VG.Proof.X448.Wide.carry f k ∧ t.gpr .x11 = 0 ∧
    t.gpr .x9 = BitVec.ofNat 64 (2 ^ 56 - 1) ∧
    Outside base o 128 s.mem t.mem ∧ Keeps VG.Proof.X448.Wide.colRegs s t
  have step : ∀ k t, k < 8 → inv k t → WP isa (.block (carryStep o k unpack)) t (inv (k + 1)) := by
    intro k t hk ⟨tl, th, tc, tz, t9, tm, tk⟩
    have ts := hs.of_keeps tk (by decide)
    have te := th k (by omega) hk
    have cap : VG.Proof.X448.Wide.coeff t.mem base TMP k + (t.gpr .x6).toNat < 2 ^ 119 := by
      rw [te, tc]
      have c := VG.Proof.X448.Wide.carry_bound (n := k) (fun i hi => hb i (by omega))
      have h := hb k hk
      omega
    refine WP.mono (VG.Proof.X448.Wide.carryStep_ok ts ho ho8 hk unpack tz t9 cap) fun u ⟨uc, uv, um, uk⟩ => ?_
    rw [te, tc] at uc uv
    refine ⟨?_, ?_, uc, (uk.1 _ (by decide)).trans tz, (uk.1 _ (by decide)).trans t9,
      tm.trans (um.mono (by omega) (by omega)), tk.trans (uk.mono (by decide))⟩
    · intro i hi
      by_cases h : i = k
      · subst i
        exact uv
      · have eq : VG.Proof.X448.Wide.coeff u.mem base o i = VG.Proof.X448.Wide.coeff t.mem base o i :=
          VG.Proof.X448.Wide.outside_coeff um (by omega) (by omega)
        rw [eq]
        exact tl i (by omega)
    · intro i hi hi'
      have sep : TMP + 16 * i + 16 ≤ o + 16 * k ∨ o + 16 * k + 16 ≤ TMP + 16 * i := by
        rcases hsep with h | h | h <;> omega
      have eq : VG.Proof.X448.Wide.coeff u.mem base TMP i = VG.Proof.X448.Wide.coeff t.mem base TMP i :=
        VG.Proof.X448.Wide.outside_coeff um sep (by simp only [TMP]; omega)
      rw [eq]
      exact th i (by omega) hi'
  rw [pass, WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Wide.passInit_ok s) fun u ⟨u6, uz, u9, um, uk⟩ => ?_
  refine WP.mono (wp_range_flatMap (M := isa) (N := 8) inv step 8 (by decide) u ?_)
    fun t ⟨tl, _, tc, _, _, tm, tk⟩ => ⟨tl, tc, tm, tk⟩
  refine ⟨fun _ hi => by omega, ?_, ?_, uz, u9, ?_, uk⟩
  · intro i _ hi; rw [um]; exact hf i hi
  · rw [u6]; rfl
  · rw [um]; exact Outside.refl _ _ _ _

end VG.Proof.X448.Wide

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Wide.Fold`. -/
section

/-! Untrusted: fold a carry into wide limbs 0 and 4. -/
namespace VG.Proof.X448.Wide

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld st TMP)
open VG.Impl.X448.AArch64.Wide VG.Proof.X448.AArch64

theorem coeff_limbs (m : Mem) (base : Addr) (o i : Nat) :
    VG.Proof.X448.Wide.coeff m base o i = limbs m base o (2 * i) + 2 ^ 64 * limbs m base o (2 * i + 1) := by
  have e0 : o + 8 * (2 * i) = o + 16 * i := by omega
  have e1 : o + 8 * (2 * i + 1) = o + 16 * i + 8 := by omega
  simp only [VG.Proof.X448.Wide.coeff, VG.Proof.X448.Wide.pair, limbs, e0, e1]

theorem foldLimb_ok {s : State} {base : Addr} (hs : Scr s base) {k : Nat} (hk : k < 8)
    (hb : VG.Proof.X448.Wide.coeff s.mem base TMP k + (s.gpr .x6).toNat < 2 ^ 64) :
    WP isa (.block [ld .x4 (TMP + 16 * k), .add .x .x4 .x4 .x6, st .x4 (TMP + 16 * k)]) s fun t =>
      (∀ i < 8, VG.Proof.X448.Wide.coeff t.mem base TMP i =
        if i = k then VG.Proof.X448.Wide.coeff s.mem base TMP i + (s.gpr .x6).toNat else VG.Proof.X448.Wide.coeff s.mem base TMP i) ∧
      Outside base TMP 128 s.mem t.mem ∧ Keeps [.x4] s t := by
  have e : TMP + 8 * (2 * k) = TMP + 16 * k := by omega
  have low : limbs s.mem base TMP (2 * k) + (s.gpr .x6).toNat < 2 ^ 64 := by
    rw [VG.Proof.X448.Wide.coeff_limbs] at hb
    omega
  have run := VG.Proof.X448.AArch64.foldLimb_ok hs (k := 2 * k) (by omega) low
  rw [e] at run
  refine WP.mono run fun t ⟨tf, tm, tk⟩ => ⟨?_, tm, tk⟩
  intro i hi
  rw [VG.Proof.X448.Wide.coeff_limbs, tf (2 * i) (by omega), tf (2 * i + 1) (by omega),
    ite_eq_right (by omega : 2 * i + 1 ≠ 2 * k), VG.Proof.X448.Wide.coeff_limbs]
  by_cases h : i = k
  · subst i
    rw [ite_eq_left rfl, ite_eq_left rfl]
    omega
  · rw [ite_eq_right (by omega : 2 * i ≠ 2 * k), ite_eq_right h]

theorem fold_ok {s : State} {base : Addr} (hs : Scr s base) {f : Nat → Nat}
    (hf : ∀ i < 8, VG.Proof.X448.Wide.coeff s.mem base TMP i = VG.Proof.X448.Wide.digit f i)
    (hc : (s.gpr .x6).toNat = VG.Proof.X448.Wide.carry f 8) (hb : VG.Proof.X448.Wide.carry f 8 < 2 ^ 63) :
    WP isa (.block fold) s fun t =>
      (∀ i < 8, VG.Proof.X448.Wide.coeff t.mem base TMP i = VG.Proof.X448.Wide.folded f i) ∧
      Outside base TMP 128 s.mem t.mem ∧ Keeps [.x4] s t := by
  have bound : ∀ i < 8, VG.Proof.X448.Wide.digit f i + VG.Proof.X448.Wide.carry f 8 < 2 ^ 64 := by
    intro i _
    have h := VG.Proof.X448.Wide.digit_lt f i
    simp only [VG.Proof.X448.Wide.radix] at h
    omega
  change WP isa (.block
    (([ld .x4 (TMP + 16 * 0), .add .x .x4 .x4 .x6,
       st .x4 (TMP + 16 * 0)] : List Instr) ++
     [ld .x4 (TMP + 16 * 4), .add .x .x4 .x4 .x6,
       st .x4 (TMP + 16 * 4)])) s _
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Wide.foldLimb_ok hs (k := 0) (by decide)
    (by rw [hf 0 (by decide), hc]; exact bound 0 (by decide))) fun u ⟨uf, um, uk⟩ => ?_
  have uc : (u.gpr .x6).toNat = VG.Proof.X448.Wide.carry f 8 := by rw [uk.1 _ (by decide), hc]
  refine WP.mono (VG.Proof.X448.Wide.foldLimb_ok (hs.of_keeps uk (by decide)) (k := 4) (by decide) ?_)
    fun t ⟨tf, tm, tk⟩ => ?_
  · rw [uf 4 (by decide), ite_eq_right (by decide), hf 4 (by decide), uc]
    exact bound 4 (by decide)
  · refine ⟨?_, um.trans tm, uk.trans tk⟩
    intro i hi
    rw [tf i hi, uf i hi, hf i hi, hc, uc]
    simp only [VG.Proof.X448.Wide.folded]
    by_cases h0 : i = 0
    · subst i; simp (config := {decide := true}) only [ite_true, ite_false]
    · by_cases h4 : i = 4
      · subst i; simp (config := {decide := true}) only [ite_true, ite_false]
      · simp only [h0, h4, ite_false, false_or, Nat.add_zero]

end VG.Proof.X448.Wide

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Wide.Normalize`. -/
section

/-! Untrusted: normalize wide coefficients and restore the field-slot interface. -/
namespace VG.Proof.X448.Wide

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ACC TMP)
open VG.Impl.X448.AArch64.Wide VG.Proof.X448.AArch64

theorem normalize_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat}
    (ho : o + 128 ≤ ACC) (ho8 : o % 8 = 0) {f : Nat → Nat}
    (hf : ∀ i < 8, VG.Proof.X448.Wide.coeff s.mem base TMP i = f i) (hb : ∀ i < 8, f i < 2 ^ 118) :
    WP isa (.block (normalize o)) s fun t =>
      (∀ i < 8, VG.Proof.X448.Wide.coeff t.mem base o i = VG.Proof.X448.Wide.encoded (VG.Proof.X448.Wide.normalized f i) true) ∧
      FieldMem base o s.mem t.mem ∧ Keeps VG.Proof.X448.Wide.colRegs s t := by
  have htmp : TMP + 128 ≤ 8192 := by decide
  have hwork : ∀ {m m' : Mem}, Outside base TMP 128 m m' → FieldMem base o m m' :=
    fun h => FieldMem.work h (by decide) (by decide)
  have keep : ∀ {a b : State}, Keeps [.x4] a b → Keeps VG.Proof.X448.Wide.colRegs a b :=
    fun h => h.mono (by decide)
  rw [normalize, List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Wide.pass_ok hs htmp (by decide) (Or.inl rfl) false hf hb) fun s₁ ⟨f₁, c₁, m₁, k₁⟩ => ?_
  simp only [VG.Proof.X448.Wide.encoded, Bool.false_eq_true, ite_false] at f₁
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Wide.fold_ok hs₁ f₁ c₁ (VG.Proof.X448.Wide.carry_bound hb)) fun s₂ ⟨f₂, m₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Wide.pass_ok hs₂ htmp (by decide) (Or.inl rfl) false f₂ (VG.Proof.X448.Wide.folded_bound hb)) fun s₃ ⟨f₃, c₃, m₃, k₃⟩ => ?_
  simp only [VG.Proof.X448.Wide.encoded, Bool.false_eq_true, ite_false] at f₃
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Wide.fold_ok hs₃ f₃ c₃ (VG.Proof.X448.Wide.carry_bound (VG.Proof.X448.Wide.folded_bound hb))) fun s₄ ⟨f₄, m₄, k₄⟩ => ?_
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  refine WP.mono (VG.Proof.X448.Wide.pass_ok hs₄ (Nat.le_trans ho (by decide)) ho8
    (Or.inr (Or.inl (Nat.le_trans ho (by decide)))) true f₄
    (VG.Proof.X448.Wide.folded_bound (VG.Proof.X448.Wide.folded_bound hb))) fun s₅ ⟨f₅, _, m₅, k₅⟩ => ?_
  exact ⟨f₅, (hwork m₁).trans ((hwork m₂).trans ((hwork m₃).trans ((hwork m₄).trans (.output m₅)))),
    k₁.trans ((keep k₂).trans (k₃.trans ((keep k₄).trans k₅)))⟩

end VG.Proof.X448.Wide

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Wide.Encoded`. -/
section

/-! Untrusted: interpreting the normalized wide output in the original slots. -/
namespace VG.Proof.X448.Wide

open VG VG.AArch64 VG.Proof.X448.AArch64

theorem decode_encoded (lo hi : BitVec 64) {v : Nat} (h : VG.Proof.X448.Wide.pair lo hi = VG.Proof.X448.Wide.encoded v true) :
    lo.toNat = v % VG.Proof.X448.radix ∧ hi.toNat = v / VG.Proof.X448.radix := by
  have hl := lo.isLt
  have hm := Nat.mod_lt v (show 0 < VG.Proof.X448.radix by decide)
  simp only [VG.Proof.X448.Wide.pair, VG.Proof.X448.Wide.encoded, ite_true, VG.Proof.X448.radix] at h hm ⊢
  omega

theorem encoded_limbs {m : Mem} {base : Addr} {o : Nat} {f : Nat → Nat}
    (hf : ∀ i < 8, VG.Proof.X448.Wide.coeff m base o i = VG.Proof.X448.Wide.encoded (f i) true) :
    ∀ i < 16, limbs m base o i = VG.Proof.X448.Wide.unpacked f i := by
  intro i hi
  have hq : i / 2 < 8 := by omega
  have dec := VG.Proof.X448.Wide.decode_encoded _ _ (hf (i / 2) hq)
  have e0 : o + 16 * (i / 2) = o + 8 * (2 * (i / 2)) := by omega
  simp only [e0] at dec
  change limbs m base o (2 * (i / 2)) = _ ∧ limbs m base o (2 * (i / 2) + 1) = _ at dec
  simp only [VG.Proof.X448.Wide.unpacked]
  split
  · rename_i h
    rw [show i = 2 * (i / 2) from by omega]
    simpa only [show (2 * (i / 2)) / 2 = i / 2 by omega] using dec.1
  · rename_i h
    rw [show i = 2 * (i / 2) + 1 from by omega]
    simpa only [show (2 * (i / 2) + 1) / 2 = i / 2 by omega] using dec.2

end VG.Proof.X448.Wide

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Wide.Mul`. -/
section

/-! Untrusted: wide field multiplication behind the existing X448 slot contract. -/
namespace VG.Proof.X448.Wide

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ACC TMP)
open VG.Impl.X448.AArch64.Wide VG.Proof.X448.AArch64
open VG.Proof.X448 (toFe_mul)

theorem mul_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat}
    (ho : VG.Proof.X448.AArch64.Slot o) (ho8 : o % 8 = 0) (ha : VG.Proof.X448.AArch64.Slot a) (ha8 : a % 8 = 0)
    (hb : VG.Proof.X448.AArch64.Slot b) (hb8 : b % 8 = 0) (ab : Bounded s.mem base a) (bb : Bounded s.mem base b) :
    WP isa (Impl.X448.AArch64.Wide.mul o a b) s fun t =>
      VG.Proof.X448.AArch64.Op base o s t ∧ Bounded t.mem base o ∧ VG.Proof.X448.AArch64.F t.mem base o = VG.Proof.X448.AArch64.F s.mem base a * VG.Proof.X448.AArch64.F s.mem base b := by
  let f := VG.Proof.X448.Wide.paired (limbs s.mem base a)
  let g := VG.Proof.X448.Wide.paired (limbs s.mem base b)
  have fa : ∀ i < 8, f i < VG.Proof.X448.Wide.radix := VG.Proof.X448.Wide.paired_bound ab
  have gb : ∀ i < 8, g i < VG.Proof.X448.Wide.radix := VG.Proof.X448.Wide.paired_bound bb
  have aw : a + 128 ≤ 8192 := Nat.le_trans ha (by decide)
  have bw : b + 128 ≤ 8192 := Nat.le_trans hb (by decide)
  rw [Impl.X448.AArch64.Wide.mul, List.append_assoc, List.append_assoc, List.append_assoc,
    WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Wide.pack_ok hs (o := PACKA) (by decide) aw (by decide) ha8
    (Or.inl (Nat.le_trans ha (by decide))) ab) fun s₁ ⟨a₁, m₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have b₁ : ∀ i < 16, limbs s₁.mem base b i = limbs s.mem base b i :=
    fun i hi => m₁.limbs (Or.inl (Nat.le_trans hb (by decide))) bw hi
  have bb₁ : Bounded s₁.mem base b := by
    intro i hi; rw [b₁ i hi]; exact bb i hi
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Wide.pack_ok hs₁ (o := PACKB) (by decide) bw (by decide) hb8
    (Or.inl (Nat.le_trans hb (by decide))) bb₁) fun s₂ ⟨b₂, m₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  have a₂ : ∀ i < 8, limbs s₂.mem base PACKA i = f i := by
    intro i hi
    have eq : limbs s₂.mem base PACKA i = limbs s₁.mem base PACKA i :=
      congrArg BitVec.toNat (m₂.word (by simp only [PACKA, PACKB]; omega) (by simp only [PACKA]; omega))
    rw [eq, a₁ i hi]
  have b₂' : ∀ i < 8, limbs s₂.mem base PACKB i = g i := by
    intro i hi
    rw [b₂ i hi]
    simp only [VG.Proof.X448.Wide.paired]
    rw [b₁ (2 * i) (by omega), b₁ (2 * i + 1) (by omega)]
    rfl
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Wide.columns_ok hs₂ (a := PACKA) (b := PACKB) (Or.inr (by decide))
    (Or.inr (by decide)) (by decide) (by decide) (by decide) (by decide)
    (by intro i hi; rw [a₂ i hi]; exact fa i hi)
    (by intro i hi; rw [b₂' i hi]; exact gb i hi)) fun s₃ ⟨c₃, m₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  have c₃' : ∀ i < 16, VG.Proof.X448.Wide.coeff s₃.mem base ACC i = VG.Proof.X448.Wide.rows f g 8 i := by
    intro i hi
    rw [c₃ i hi]
    exact VG.Proof.X448.Wide.rows_congr a₂ b₂' (by decide) i
  have raw : ∀ i < 16, VG.Proof.X448.Wide.coeff s₃.mem base ACC i < 2 ^ 116 := by
    intro i hi
    rw [c₃' i hi]
    exact Nat.lt_of_le_of_lt (VG.Proof.X448.Wide.rows_bound fa gb (by decide) i) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Wide.reduce_ok hs₃ raw) fun s₄ ⟨r₄, m₄, k₄⟩ => ?_
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  have red := VG.Proof.X448.Wide.reduced_bound raw
  refine WP.mono (VG.Proof.X448.Wide.normalize_ok hs₄ ho ho8 r₄ red) fun t ⟨tf, tm, tk⟩ => ?_
  have out := VG.Proof.X448.Wide.encoded_limbs tf
  have val : VG.Proof.X448.AArch64.fe t.mem base o % Spec.X448.P =
      (VG.Proof.X448.AArch64.fe s.mem base a * VG.Proof.X448.AArch64.fe s.mem base b) % Spec.X448.P := by
    rw [show VG.Proof.X448.AArch64.fe t.mem base o = VG.Proof.X448.valN
        (VG.Proof.X448.Wide.unpacked (VG.Proof.X448.Wide.normalized (VG.Proof.X448.Wide.reduced (VG.Proof.X448.Wide.coeff s₃.mem base ACC)))) 16 from
        VG.Proof.X448.valN_congr out,
      VG.Proof.X448.Wide.unpacked_val, VG.Proof.X448.Wide.normalized_mod red, VG.Proof.X448.Wide.reduced_mod,
      VG.Proof.X448.Wide.valN_congr c₃', VG.Proof.X448.Wide.rows_val f g (by decide), VG.Proof.X448.Wide.paired_val, VG.Proof.X448.Wide.paired_val]
  refine ⟨⟨?_, ?_⟩, ?_, VG.Proof.X448.toFe_mul val⟩
  · exact (k₁.mono (by decide)).trans ((k₂.mono (by decide)).trans
      ((k₃.mono (by decide)).trans ((k₄.mono (by decide)).trans (tk.mono (by decide)))))
  · exact (FieldMem.work m₁ (by decide) (by decide)).trans
      ((FieldMem.work m₂ (by decide) (by decide)).trans
      ((FieldMem.work m₃ (by decide) (by decide)).trans
      ((FieldMem.work m₄ (by decide) (by decide)).trans tm)))
  · intro i hi
    rw [out i hi]
    exact VG.Proof.X448.Wide.unpacked_bound (fun j _ => VG.Proof.X448.Wide.digit_lt _ j) i hi

end VG.Proof.X448.Wide

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Wide.Representation`. -/
section

/-!
# Headroom-aware X448 field representation

Untrusted: this is an internal arithmetic contract for an eight-word backend.
A representative has a value modulo p and a separate, explicit coefficient
bound. Weak reduction need not normalize every coefficient below the radix.
The public RFC 7748 contract and existing backend contract are unchanged.
-/
namespace VG.Proof.X448.Wide.Representation
open VG.Spec.X448
open VG.Proof.X448 (toFe)

/-- Coefficient headroom, independent of the represented field value. -/
def Within (bound : Nat) (f : Nat → Nat) : Prop := ∀ i < 8, f i < bound

/-- The same field element may have many noncanonical representatives. -/
def Represents (f : Nat → Nat) (x : VG.Spec.X448.Fe) : Prop := VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN f 8) = x

/-- Conservative weak bound, closed under the add/sub contracts below. -/
def weakBound : Nat := VG.Proof.X448.Wide.radix + 32

/-- The contract an eight-word weakly reduced field operation maintains. -/
structure Weak (f : Nat → Nat) (x : VG.Spec.X448.Fe) : Prop where
  value : VG.Proof.X448.Wide.Representation.Represents f x
  limbs : VG.Proof.X448.Wide.Representation.Within VG.Proof.X448.Wide.Representation.weakBound f

/-- Distribute old carries independently, then fold the top one into 0 and 4.
This is a mathematical weak-reduction schedule, not the existing serial pass
and not a transcription of OpenSSL's instruction schedule. -/
def weakReduce (f : Nat → Nat) (i : Nat) : Nat :=
  f i % VG.Proof.X448.Wide.radix + (if i = 0 then f 7 / VG.Proof.X448.Wide.radix else f (i - 1) / VG.Proof.X448.Wide.radix) +
    (if i = 4 then f 7 / VG.Proof.X448.Wide.radix else 0)

theorem weakReduce_val (f : Nat → Nat) :
    VG.Proof.X448.Wide.valN (VG.Proof.X448.Wide.Representation.weakReduce f) 8 + VG.Spec.X448.P * (f 7 / VG.Proof.X448.Wide.radix) = VG.Proof.X448.Wide.valN f 8 := by
  have h0 := Nat.mod_add_div (f 0) VG.Proof.X448.Wide.radix
  have h1 := Nat.mod_add_div (f 1) VG.Proof.X448.Wide.radix
  have h2 := Nat.mod_add_div (f 2) VG.Proof.X448.Wide.radix
  have h3 := Nat.mod_add_div (f 3) VG.Proof.X448.Wide.radix
  have h4 := Nat.mod_add_div (f 4) VG.Proof.X448.Wide.radix
  have h5 := Nat.mod_add_div (f 5) VG.Proof.X448.Wide.radix
  have h6 := Nat.mod_add_div (f 6) VG.Proof.X448.Wide.radix
  have h7 := Nat.mod_add_div (f 7) VG.Proof.X448.Wide.radix
  simp only [VG.Proof.X448.Wide.radix, Nat.reducePow] at h0 h1 h2 h3 h4 h5 h6 h7
  have hp : VG.Spec.X448.P = VG.Proof.X448.Wide.radix ^ 8 - VG.Proof.X448.Wide.radix ^ 4 - 1 := by decide +kernel
  simp only [VG.Proof.X448.Wide.valN, VG.Proof.X448.Wide.Representation.weakReduce, Nat.reduceSub, Nat.reduceEqDiff, ite_true, ite_false,
    Nat.pow_zero, Nat.zero_add, Nat.one_mul, Nat.add_zero, hp, VG.Proof.X448.Wide.radix, Nat.reducePow, Nat.reduceSub]
  omega

theorem weakReduce_mod (f : Nat → Nat) :
    VG.Proof.X448.Wide.valN (VG.Proof.X448.Wide.Representation.weakReduce f) 8 % VG.Spec.X448.P = VG.Proof.X448.Wide.valN f 8 % VG.Spec.X448.P := by
  rw [← VG.Proof.X448.Wide.Representation.weakReduce_val f, Nat.add_mul_mod_self_left]

theorem weakReduce_represents {f : Nat → Nat} {x : VG.Spec.X448.Fe} (h : VG.Proof.X448.Wide.Representation.Represents f x) :
    VG.Proof.X448.Wide.Representation.Represents (VG.Proof.X448.Wide.Representation.weakReduce f) x := by
  exact (VG.Proof.X448.toFe_congr (VG.Proof.X448.Wide.Representation.weakReduce_mod f)).trans h

/-- Public integer headroom controls both old carries at each output limb. -/
theorem weakReduce_bound {f : Nat → Nat} {h : Nat}
    (hf : VG.Proof.X448.Wide.Representation.Within (VG.Proof.X448.Wide.radix * h) f) (hh : 1 ≤ h) :
    VG.Proof.X448.Wide.Representation.Within (VG.Proof.X448.Wide.radix + 2 * (h - 1)) (VG.Proof.X448.Wide.Representation.weakReduce f) := by
  intro i hi
  have low := Nat.mod_lt (f i) (show 0 < VG.Proof.X448.Wide.radix by decide)
  have top : f 7 / VG.Proof.X448.Wide.radix < h := (Nat.div_lt_iff_lt_mul (by decide)).mpr (by
    simpa only [Nat.mul_comm] using hf 7 (by decide))
  have prev : f (i - 1) / VG.Proof.X448.Wide.radix < h := (Nat.div_lt_iff_lt_mul (by decide)).mpr (by
    simpa only [Nat.mul_comm] using hf (i - 1) (by omega))
  simp only [VG.Proof.X448.Wide.Representation.weakReduce]
  split <;> split <;> omega

/-- Addition may enter the reducer with almost three radix units of headroom. -/
theorem add_weak_bound {f g : Nat → Nat} (hf : VG.Proof.X448.Wide.Representation.Within VG.Proof.X448.Wide.Representation.weakBound f) (hg : VG.Proof.X448.Wide.Representation.Within VG.Proof.X448.Wide.Representation.weakBound g) :
    VG.Proof.X448.Wide.Representation.Within VG.Proof.X448.Wide.Representation.weakBound (VG.Proof.X448.Wide.Representation.weakReduce (fun i => f i + g i)) := by
  have cap : VG.Proof.X448.Wide.Representation.Within (VG.Proof.X448.Wide.radix * 3) (fun i => f i + g i) := by
    intro i hi
    have a := hf i hi; have b := hg i hi
    simp only [VG.Proof.X448.Wide.Representation.weakBound, VG.Proof.X448.Wide.radix] at a b ⊢
    omega
  have out := VG.Proof.X448.Wide.Representation.weakReduce_bound cap (by decide : 1 ≤ 3)
  intro i hi
  exact Nat.lt_of_lt_of_le (out i hi) (by simp only [VG.Proof.X448.Wide.Representation.weakBound]; omega)

/-- Four times p leaves room for weak limbs during nonnegative subtraction. -/
def bias (i : Nat) : Nat := if i = 4 then 4 * VG.Proof.X448.Wide.radix - 8 else 4 * VG.Proof.X448.Wide.radix - 4

def difference (f g : Nat → Nat) (i : Nat) : Nat := f i + VG.Proof.X448.Wide.Representation.bias i - g i

theorem difference_weak_bound {f g : Nat → Nat} (hf : VG.Proof.X448.Wide.Representation.Within VG.Proof.X448.Wide.Representation.weakBound f) :
    VG.Proof.X448.Wide.Representation.Within VG.Proof.X448.Wide.Representation.weakBound (VG.Proof.X448.Wide.Representation.weakReduce (VG.Proof.X448.Wide.Representation.difference f g)) := by
  have cap : VG.Proof.X448.Wide.Representation.Within (VG.Proof.X448.Wide.radix * 6) (VG.Proof.X448.Wide.Representation.difference f g) := by
    intro i hi
    have a := hf i hi
    simp only [VG.Proof.X448.Wide.Representation.difference, VG.Proof.X448.Wide.Representation.bias]
    split <;> simp only [VG.Proof.X448.Wide.Representation.weakBound, VG.Proof.X448.Wide.radix] at a ⊢ <;> omega
  have out := VG.Proof.X448.Wide.Representation.weakReduce_bound cap (by decide : 1 ≤ 6)
  intro i hi
  exact Nat.lt_of_lt_of_le (out i hi) (by simp only [VG.Proof.X448.Wide.Representation.weakBound]; omega)

theorem add_ok {f g : Nat → Nat} {x y : VG.Spec.X448.Fe} (hf : VG.Proof.X448.Wide.Representation.Weak f x) (hg : VG.Proof.X448.Wide.Representation.Weak g y) :
    VG.Proof.X448.Wide.Representation.Weak (VG.Proof.X448.Wide.Representation.weakReduce (fun i => f i + g i)) (x + y) := by
  refine ⟨?_, VG.Proof.X448.Wide.Representation.add_weak_bound hf.limbs hg.limbs⟩
  unfold VG.Proof.X448.Wide.Representation.Represents
  have h := VG.Proof.X448.toFe_add (a := VG.Proof.X448.Wide.valN f 8) (b := VG.Proof.X448.Wide.valN g 8)
    (c := VG.Proof.X448.Wide.valN (VG.Proof.X448.Wide.Representation.weakReduce (fun i => f i + g i)) 8) (by
      rw [VG.Proof.X448.Wide.Representation.weakReduce_mod, VG.Proof.X448.Wide.valN_add])
  exact h.trans (congrArg₂ (· + ·) hf.value hg.value)

theorem bias_val : VG.Proof.X448.Wide.valN VG.Proof.X448.Wide.Representation.bias 8 = 4 * VG.Spec.X448.P := by decide +kernel

theorem bias_ge (i : Nat) : VG.Proof.X448.Wide.Representation.weakBound ≤ VG.Proof.X448.Wide.Representation.bias i := by
  simp only [VG.Proof.X448.Wide.Representation.bias]
  split <;> decide +kernel

theorem difference_val {f g : Nat → Nat} (hg : VG.Proof.X448.Wide.Representation.Within VG.Proof.X448.Wide.Representation.weakBound g) :
    VG.Proof.X448.Wide.valN (VG.Proof.X448.Wide.Representation.difference f g) 8 + VG.Proof.X448.Wide.valN g 8 = VG.Proof.X448.Wide.valN f 8 + 4 * VG.Spec.X448.P := by
  rw [← VG.Proof.X448.Wide.valN_add]
  have eq : VG.Proof.X448.Wide.valN (fun i => VG.Proof.X448.Wide.Representation.difference f g i + g i) 8 =
      VG.Proof.X448.Wide.valN (fun i => f i + VG.Proof.X448.Wide.Representation.bias i) 8 := by
    apply VG.Proof.X448.Wide.valN_congr
    intro i hi
    have h := hg i hi
    have b := VG.Proof.X448.Wide.Representation.bias_ge i
    simp only [VG.Proof.X448.Wide.Representation.difference]
    omega
  rw [eq, VG.Proof.X448.Wide.valN_add, VG.Proof.X448.Wide.Representation.bias_val]

theorem sub_ok {f g : Nat → Nat} {x y : VG.Spec.X448.Fe} (hf : VG.Proof.X448.Wide.Representation.Weak f x) (hg : VG.Proof.X448.Wide.Representation.Weak g y) :
    VG.Proof.X448.Wide.Representation.Weak (VG.Proof.X448.Wide.Representation.weakReduce (VG.Proof.X448.Wide.Representation.difference f g)) (x - y) := by
  refine ⟨?_, VG.Proof.X448.Wide.Representation.difference_weak_bound hf.limbs⟩
  unfold VG.Proof.X448.Wide.Representation.Represents
  have hm : (VG.Proof.X448.Wide.valN (VG.Proof.X448.Wide.Representation.weakReduce (VG.Proof.X448.Wide.Representation.difference f g)) 8 + VG.Proof.X448.Wide.valN g 8) % VG.Spec.X448.P = VG.Proof.X448.Wide.valN f 8 % VG.Spec.X448.P := by
    rw [Nat.add_mod, VG.Proof.X448.Wide.Representation.weakReduce_mod, ← Nat.add_mod, VG.Proof.X448.Wide.Representation.difference_val hg.limbs,
      Nat.mul_comm 4 VG.Spec.X448.P, Nat.add_mul_mod_self_left]
  exact (VG.Proof.X448.toFe_sub hm).trans (congrArg₂ (· - ·) hf.value hg.value)

/-- Existing full normalization is a conversion from broad coefficients to
normalized limbs; normalized output is also a valid weak representative. -/
theorem normalize_within_weak (f : Nat → Nat) : VG.Proof.X448.Wide.Representation.Within VG.Proof.X448.Wide.Representation.weakBound (VG.Proof.X448.Wide.normalized f) := by
  intro i _
  exact Nat.lt_trans (VG.Proof.X448.Wide.digit_lt _ i) (by simp only [VG.Proof.X448.Wide.Representation.weakBound]; omega)

/-- Full normalization preserves the field value while tightening the bound. -/
theorem normalize_ok {f : Nat → Nat} {x : VG.Spec.X448.Fe}
    (h : VG.Proof.X448.Wide.Representation.Within (2 ^ 118) f) (hx : VG.Proof.X448.Wide.Representation.Represents f x) : VG.Proof.X448.Wide.Representation.Weak (VG.Proof.X448.Wide.normalized f) x :=
  ⟨(VG.Proof.X448.toFe_congr (VG.Proof.X448.Wide.normalized_mod h)).trans hx, VG.Proof.X448.Wide.Representation.normalize_within_weak f⟩

/-- The second serial carry pass has at most one carry-out. -/
theorem second_carry {f : Nat → Nat} (h : VG.Proof.X448.Wide.Representation.Within (2 ^ 118) f) :
    VG.Proof.X448.Wide.carry (VG.Proof.X448.Wide.folded f) 8 ≤ 1 := by
  have c0 := VG.Proof.X448.Wide.carry_bound h
  have v0 := VG.Proof.X448.Wide.valN_lt (n := 8) (fun i _ => VG.Proof.X448.Wide.digit_lt f i)
  have e1 := VG.Proof.X448.Wide.pass_eq (VG.Proof.X448.Wide.folded f) 8
  rw [VG.Proof.X448.Wide.folded_val] at e1
  change VG.Proof.X448.Wide.valN (VG.Proof.X448.Wide.digit f) 8 < VG.Proof.X448.Wide.full at v0
  change VG.Proof.X448.Wide.valN (VG.Proof.X448.Wide.digit (VG.Proof.X448.Wide.folded f)) 8 + VG.Proof.X448.Wide.full * VG.Proof.X448.Wide.carry (VG.Proof.X448.Wide.folded f) 8 = _ at e1
  have small : (VG.Proof.X448.Wide.half + 1) * (2 ^ 63 + 1) < VG.Proof.X448.Wide.full := by decide +kernel
  by_contra hc
  have hb := Nat.mul_le_mul_left (VG.Proof.X448.Wide.half + 1) (Nat.le_of_lt c0)
  have hp := Nat.mul_le_mul_left VG.Proof.X448.Wide.full (show 2 ≤ VG.Proof.X448.Wide.carry (VG.Proof.X448.Wide.folded f) 8 from by omega)
  omega

/-- Two carry passes and folds suffice for a weak field representative. -/
theorem twice_weak {f : Nat → Nat} (h : VG.Proof.X448.Wide.Representation.Within (2 ^ 118) f) :
    VG.Proof.X448.Wide.Representation.Within VG.Proof.X448.Wide.Representation.weakBound (VG.Proof.X448.Wide.folded (VG.Proof.X448.Wide.folded f)) := by
  have hc := VG.Proof.X448.Wide.Representation.second_carry h
  intro i _
  have hd := VG.Proof.X448.Wide.digit_lt (VG.Proof.X448.Wide.folded f) i
  simp only [VG.Proof.X448.Wide.folded, VG.Proof.X448.Wide.Representation.weakBound]
  split <;> omega

theorem twice_mod (f : Nat → Nat) :
    VG.Proof.X448.Wide.valN (VG.Proof.X448.Wide.folded (VG.Proof.X448.Wide.folded f)) 8 % VG.Spec.X448.P = VG.Proof.X448.Wide.valN f 8 % VG.Spec.X448.P := by
  rw [VG.Proof.X448.Wide.folded_mod, VG.Proof.X448.Wide.folded_mod]

end VG.Proof.X448.Wide.Representation

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Wide.SymmetricColumn`. -/
section

/-! Untrusted: store a symmetric square diagonal. -/
namespace VG.Proof.X448.Wide
open VG VG.AArch64
open VG.Impl.X448.AArch64 (ACC)
open VG.Impl.X448.AArch64.Wide VG.Impl.X448.AArch64.Cached VG.Proof.X448.AArch64

theorem symmetricColumn_ok {s : State} {base : Addr} (hs : Scr s base) {f : Nat → Nat} {k : Nat}
    (hk : k < 16) (fc : ∀ i < 8, (s.gpr (cacheReg i)).toNat = f i)
    (fb : ∀ i < 8, f i < VG.Proof.X448.Wide.radix) :
    WP isa (.block (Impl.X448.AArch64.Symmetric.column k)) s fun t =>
      VG.Proof.X448.Wide.coeff t.mem base ACC k = VG.Proof.X448.Wide.rows f f 8 k ∧
      Outside base (ACC + 16 * k) 16 s.mem t.mem ∧ Keeps VG.Proof.X448.Wide.termRegs s t := by
  rw [Impl.X448.AArch64.Symmetric.column, List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Wide.zero_ok s) fun u ⟨uz, um, uk⟩ => ?_
  rw [WP.block_append_iff]
  have uk' : Keeps VG.Proof.X448.Wide.termRegs s u := uk.mono (by decide)
  refine WP.mono (VG.Proof.X448.Wide.accumSquareBody_ok hk (by
    intro i hi; rw [uk'.1 _ (VG.Proof.X448.Wide.cacheReg_kept hi)]; exact fc i hi) fb (by decide) uz)
    fun v ⟨vv, vm, vk⟩ => ?_
  have vs := (hs.of_keeps uk (by decide)).of_keeps vk (by decide)
  refine WP.mono (VG.Proof.X448.Wide.store_ok vs hk) fun t ⟨tm, tk⟩ => ?_
  refine ⟨?_, ?_, uk'.trans (vk.trans (tk.mono (by decide)))⟩
  · rw [tm, VG.Proof.X448.Wide.coeff_put _ base _ _ (by simp only [ACC]; omega)
      (by simp only [ACC]; omega), ite_eq_left rfl, vv, Nat.zero_add]
  · rw [tm, vm, um]
    exact VG.Proof.X448.Wide.putCoeff_outside _ _ _ _ (by simp only [ACC]; omega)
end VG.Proof.X448.Wide

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Wide.SymmetricColumns`. -/
section

/-! Untrusted: the complete two-word coefficient array of a wide product. -/
namespace VG.Proof.X448.Wide

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ACC)
open VG.Impl.X448.AArch64.Wide VG.Proof.X448.AArch64

theorem symmetricColumns_ok {s : State} {base : Addr} (hs : Scr s base) {f : Nat → Nat}
    (fc : ∀ i < 8, (s.gpr (Impl.X448.AArch64.Cached.cacheReg i)).toNat = f i)
    (fb : ∀ i < 8, f i < VG.Proof.X448.Wide.radix) :
    WP isa (.block ((List.range 16).flatMap (Impl.X448.AArch64.Symmetric.column))) s fun t =>
      (∀ k < 16, VG.Proof.X448.Wide.coeff t.mem base ACC k = VG.Proof.X448.Wide.rows f f 8 k) ∧
      Outside base ACC 256 s.mem t.mem ∧ Keeps VG.Proof.X448.Wide.termRegs s t := by
  let inv := fun n (t : State) =>
    (∀ k < 16, VG.Proof.X448.Wide.coeff t.mem base ACC k = if k < n then VG.Proof.X448.Wide.rows f f 8 k else VG.Proof.X448.Wide.coeff s.mem base ACC k) ∧
    Outside base ACC 256 s.mem t.mem ∧ Keeps VG.Proof.X448.Wide.termRegs s t
  have step : ∀ n t, n < 16 → inv n t → WP isa (.block (Impl.X448.AArch64.Symmetric.column n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    refine WP.mono (VG.Proof.X448.Wide.symmetricColumn_ok (hs.of_keeps tk (by decide)) hn (by
      intro i hi; rw [tk.1 _ (VG.Proof.X448.Wide.cacheReg_kept hi)]; exact fc i hi) fb) fun u ⟨uv, um, uk⟩ => ?_
    refine ⟨?_, tm.trans (um.mono (by omega) (by omega)), tk.trans uk⟩
    intro k hk
    by_cases h : k = n
    · subst k
      rw [ite_eq_left (by omega), uv]

    · have hsep : ACC + 16 * k + 16 ≤ ACC + 16 * n ∨
          ACC + 16 * n + 16 ≤ ACC + 16 * k := by omega
      change VG.Proof.X448.Wide.pair (word u.mem base (ACC + 16 * k)) (word u.mem base (ACC + 16 * k + 8)) = _
      rw [VG.Proof.X448.Wide.outside_coeff um hsep (by simp only [ACC]; omega)]
      change VG.Proof.X448.Wide.coeff t.mem base ACC k = _
      rw [tf k hk]
      have e : (k < n) = (k < n + 1) := propext (by omega)
      simp only [e]
  have init : inv 0 s := ⟨by intro k _; rw [ite_eq_right (by omega)], Outside.refl _ _ _ _, Keeps.refl _ _⟩
  refine WP.mono (wp_range_flatMap (M := isa) (N := 16) inv step 16 (by decide) s init)
    fun t ⟨tf, tm, tk⟩ => ?_
  exact ⟨fun k hk => (tf k hk).trans (ite_eq_left hk), tm, tk⟩

end VG.Proof.X448.Wide

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Wide.TailBounds`. -/
section

/-! Untrusted: tighter carry bounds for coefficients after the first fold. -/
namespace VG.Proof.X448.Wide

theorem carry_small {f : Nat → Nat} {n : Nat} (h : ∀ i < n, f i < 2 ^ 63 + VG.Proof.X448.Wide.radix) :
    VG.Proof.X448.Wide.carry f n < 2 ^ 8 := by
  induction n with
  | zero => simp only [VG.Proof.X448.Wide.carry]; decide
  | succ n ih =>
    have hi := ih (fun i hi => h i (by omega))
    have hn := h n (by omega)
    simp only [VG.Proof.X448.Wide.carry, VG.Proof.X448.Wide.radix]
    simp only [VG.Proof.X448.Wide.radix] at hn
    omega

theorem folded_small {f : Nat → Nat} (h : ∀ i < 8, f i < 2 ^ 118) :
    ∀ i < 8, VG.Proof.X448.Wide.folded f i < 2 ^ 63 + VG.Proof.X448.Wide.radix := by
  have hc := VG.Proof.X448.Wide.carry_bound h
  intro i _
  have hd := VG.Proof.X448.Wide.digit_lt f i
  simp only [VG.Proof.X448.Wide.folded]
  split <;> omega

end VG.Proof.X448.Wide

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Wide.TailRegs`. -/
section

/-! Untrusted: a one-word carry step after wide reduction. -/
namespace VG.Proof.X448.Wide

open VG VG.AArch64 VG.Proof.X448.AArch64

theorem pair_low64 (lo hi : BitVec 64) (h : VG.Proof.X448.Wide.pair lo hi < 2 ^ 64) :
    hi.toNat = 0 ∧ lo.toNat = VG.Proof.X448.Wide.pair lo hi := by
  simp only [VG.Proof.X448.Wide.pair] at h ⊢
  omega

theorem tailRegs_ok (s : State) (hm : s.gpr .x9 = BitVec.ofNat 64 (2 ^ 56 - 1))
    (hb : (s.gpr .x4).toNat + (s.gpr .x6).toNat < 2 ^ 64) :
    let v := (s.gpr .x4).toNat + (s.gpr .x6).toNat
    WP isa (.block Impl.X448.AArch64.Tail.regs) s fun t =>
      (t.gpr .x4).toNat = v % VG.Proof.X448.Wide.radix ∧ (t.gpr .x6).toNat = v / VG.Proof.X448.Wide.radix ∧
      t.mem = s.mem ∧ Keeps [.x4, .x6] s t := by
  intro v
  have hv : (s.gpr .x4 + s.gpr .x6).toNat = v := by rw [BitVec.toNat_add, Nat.mod_eq_of_lt hb]
  have hd := VG.Proof.X448.Wide.low56 (s.gpr .x4 + s.gpr .x6) 0
  simp only [VG.Proof.X448.Wide.pair, show (0 : BitVec 64).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero, hv] at hd
  have hc : ((s.gpr .x4 + s.gpr .x6) >>> 56).toNat = v / VG.Proof.X448.Wide.radix := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hv]
    rfl
  apply WP.of_runBlock
  simp only [Impl.X448.AArch64.Tail.regs, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.read, Size.bits, RegUpd.gpr_write, BitVec.setWidth_eq, ite_true, ite_false,
    reduceCtorEq, Nat.reduceLT, hm, Option.some.injEq, exists_eq_left']
  refine ⟨hd, hc, rfl, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

end VG.Proof.X448.Wide

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Wide.TailStep`. -/
section

/-! Untrusted: narrow carry steps whose input coefficient already fits in one word. -/
namespace VG.Proof.X448.Wide

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld st TMP)
open VG.Proof.X448.AArch64

theorem loadLow_ok {s : State} {base : Addr} (hs : Scr s base) {i : Nat} (hi : i < 8)
    (hb : VG.Proof.X448.Wide.coeff s.mem base TMP i < 2 ^ 64) :
    WP isa (.block [ld .x4 (TMP + 16 * i)]) s fun t =>
      (t.gpr .x4).toNat = VG.Proof.X448.Wide.coeff s.mem base TMP i ∧ t.mem = s.mem ∧ Keeps [.x4] s t := by
  have ae : (TMP + 16 * i) % 8 = 0 ∧ TMP + 16 * i < 32768 := by simp only [TMP]; omega
  have al := hs.read (d := TMP + 16 * i) (n := 8) (by simp only [TMP]; omega)
  have low := (VG.Proof.X448.Wide.pair_low64 _ _ hb).2
  apply WP.of_runBlock
  simp only [ld, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
    ae, and_self, State.load, hs.x3, al, ite_true, Option.map_some,
    Option.bind_some, BitVec.setWidth_eq, read8_eq, RegUpd.gpr_write,
    Option.some.injEq, exists_eq_left']
  refine ⟨low, rfl, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

theorem storeLow_ok {s : State} {base : Addr} (hs : Scr s base) {i : Nat} (hi : i < 8) :
    WP isa (.block [st .x4 (TMP + 16 * i)]) s fun t =>
      t.mem = s.mem.writeW (off base (TMP + 16 * i)) (s.gpr .x4) ∧ Keeps [] s t := by
  have ae : (TMP + 16 * i) % 8 = 0 ∧ TMP + 16 * i < 32768 := by simp only [TMP]; omega
  have aw := hs.write (d := TMP + 16 * i) (n := 8) (by simp only [TMP]; omega)
  apply WP.of_runBlock
  simp only [st, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
    ae, and_self, State.read, State.store, hs.x3, aw, ite_true,
    Option.bind_some, BitVec.setWidth_eq, write8_eq, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, (fun _ _ => rfl), rfl, rfl⟩

theorem tailStep_ok {s : State} {base : Addr} (hs : Scr s base) {o i : Nat}
    (ho : o + 128 ≤ 8192) (ho8 : o % 8 = 0) (hi : i < 8) (unpack : Bool)
    (hfalse : unpack = false → o = TMP)
    (hm : s.gpr .x9 = BitVec.ofNat 64 (2 ^ 56 - 1))
    (hb : VG.Proof.X448.Wide.coeff s.mem base TMP i + (s.gpr .x6).toNat < 2 ^ 64) :
    let v := VG.Proof.X448.Wide.coeff s.mem base TMP i + (s.gpr .x6).toNat
    WP isa (.block (Impl.X448.AArch64.Tail.step o i unpack)) s fun t =>
      (t.gpr .x6).toNat = v / VG.Proof.X448.Wide.radix ∧ VG.Proof.X448.Wide.coeff t.mem base o i = VG.Proof.X448.Wide.encoded (v % VG.Proof.X448.Wide.radix) unpack ∧
      Outside base (o + 16 * i) 16 s.mem t.mem ∧ Keeps [.x4, .x5, .x6] s t := by
  intro v
  have hb' : VG.Proof.X448.Wide.coeff s.mem base TMP i < 2 ^ 64 := by omega
  have high := (VG.Proof.X448.Wide.pair_low64 _ _ hb').1
  rw [Impl.X448.AArch64.Tail.step, List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Wide.loadLow_ok hs hi hb') fun u ⟨uv, um, uk⟩ => ?_
  rw [WP.block_append_iff]
  have u9 := (uk.1 .x9 (by decide)).trans hm
  have raw : (u.gpr .x4).toNat + (u.gpr .x6).toNat = v := by
    rw [uv, uk.1 .x6 (by decide)]
  refine WP.mono (VG.Proof.X448.Wide.tailRegs_ok u u9 (by rw [raw]; exact hb)) fun w ⟨w4, w6, wm, wk⟩ => ?_
  rw [raw] at w4 w6
  have ws := (hs.of_keeps uk (by decide)).of_keeps wk (by decide)
  have keep : Keeps [.x4, .x5, .x6] s w := (uk.mono (by decide)).trans (wk.mono (by decide))
  cases unpack with
  | false =>
    have e := hfalse rfl
    subst o
    rw [ite_eq_right (by decide)]
    refine WP.mono (VG.Proof.X448.Wide.storeLow_ok ws hi) fun t ⟨tm, tk⟩ => ?_
    refine ⟨?_, ?_, ?_, keep.trans (tk.mono (by decide))⟩
    · rw [tk.1 .x6 (by decide)]; exact w6
    · rw [tm]
      have out := writeW_outside w.mem base (w.gpr .x4) (d := TMP + 16 * i) (by simp only [TMP]; omega)
      have lo : word (w.mem.writeW (off base (TMP + 16 * i)) (w.gpr .x4)) base (TMP + 16 * i) = w.gpr .x4 :=
        Mem.readW_writeW_self64 _ _ _
      have eh := out.word (d := TMP + 16 * i + 8) (Or.inr (by omega)) (by simp only [TMP]; omega)
      change VG.Proof.X448.Wide.pair (word _ base (TMP + 16 * i)) (word _ base (TMP + 16 * i + 8)) = _
      rw [lo, eh, wm, um]
      simp only [VG.Proof.X448.Wide.pair, high, Nat.mul_zero, Nat.add_zero, VG.Proof.X448.Wide.encoded, Bool.false_eq_true, ite_false]
      exact w4
    · rw [tm, wm, um]
      exact (writeW_outside _ _ _ (by simp only [TMP]; omega)).mono (by omega) (by omega)
  | true =>
    rw [ite_eq_left (by decide), show
      [.lsr .x .x5 .x4 28, .logic .and .x .x4 .x4 .x12, st .x4 (o + 16 * i), st .x5 (o + 16 * i + 8)] =
      [.lsr .x .x5 .x4 28, .logic .and .x .x4 .x4 .x12] ++
        [st .x4 (o + 16 * i), st .x5 (o + 16 * i + 8)] from rfl, WP.block_append_iff]
    refine WP.mono (VG.Proof.X448.Wide.unpackRegs_ok ws) fun z ⟨z4, z5, zm, zk⟩ => ?_
    have zs := ws.of_keeps zk (by decide)
    refine WP.mono (VG.Proof.X448.Wide.storeAt_ok zs (k := i) (by omega) ho8) fun t ⟨tm, tk⟩ => ?_
    refine ⟨?_, ?_, ?_, keep.trans ((zk.mono (by decide)).trans (tk.mono (by decide)))⟩
    · rw [tk.1 .x6 (by decide), zk.1 .x6 (by decide)]; exact w6
    · rw [tm, VG.Proof.X448.Wide.coeff_put _ base _ _ (by omega) (by omega), ite_eq_left rfl]
      simp only [VG.Proof.X448.Wide.pair, VG.Proof.X448.Wide.encoded, ite_true]
      rw [z4, z5, w4]
    · rw [tm, zm, wm, um]
      exact VG.Proof.X448.Wide.putCoeff_outside _ _ _ _ (by omega)

end VG.Proof.X448.Wide

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Wide.TailPass`. -/
section

/-! Untrusted: in-place or disjoint wide carry propagation. -/
namespace VG.Proof.X448.Wide

open VG VG.AArch64
open VG.Impl.X448.AArch64 (TMP)
open VG.Impl.X448.AArch64.Wide VG.Proof.X448.AArch64

theorem tailPass_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat}
    (ho : o + 128 ≤ 8192) (ho8 : o % 8 = 0)
    (hsep : o = TMP ∨ o + 128 ≤ TMP ∨ TMP + 128 ≤ o) (unpack : Bool)
    (hfalse : unpack = false → o = TMP)
    {f : Nat → Nat} (hf : ∀ i < 8, VG.Proof.X448.Wide.coeff s.mem base TMP i = f i)
    (hb : ∀ i < 8, f i < 2 ^ 63 + VG.Proof.X448.Wide.radix) :
    WP isa (.block (Impl.X448.AArch64.Tail.pass o unpack)) s fun t =>
      (∀ i < 8, VG.Proof.X448.Wide.coeff t.mem base o i = VG.Proof.X448.Wide.encoded (VG.Proof.X448.Wide.digit f i) unpack) ∧
      (t.gpr .x6).toNat = VG.Proof.X448.Wide.carry f 8 ∧ Outside base o 128 s.mem t.mem ∧ Keeps VG.Proof.X448.Wide.colRegs s t := by
  let inv := fun k (t : State) =>
    (∀ i < k, VG.Proof.X448.Wide.coeff t.mem base o i = VG.Proof.X448.Wide.encoded (VG.Proof.X448.Wide.digit f i) unpack) ∧
    (∀ i, k ≤ i → i < 8 → VG.Proof.X448.Wide.coeff t.mem base TMP i = f i) ∧
    (t.gpr .x6).toNat = VG.Proof.X448.Wide.carry f k ∧ t.gpr .x11 = 0 ∧
    t.gpr .x9 = BitVec.ofNat 64 (2 ^ 56 - 1) ∧
    Outside base o 128 s.mem t.mem ∧ Keeps VG.Proof.X448.Wide.colRegs s t
  have step : ∀ k t, k < 8 → inv k t → WP isa (.block (Impl.X448.AArch64.Tail.step o k unpack)) t (inv (k + 1)) := by
    intro k t hk ⟨tl, th, tc, tz, t9, tm, tk⟩
    have ts := hs.of_keeps tk (by decide)
    have te := th k (by omega) hk
    have cap : VG.Proof.X448.Wide.coeff t.mem base TMP k + (t.gpr .x6).toNat < 2 ^ 64 := by
      rw [te, tc]
      have c := VG.Proof.X448.Wide.carry_small (n := k) (fun i hi => hb i (by omega))
      have h := hb k hk
      simp only [VG.Proof.X448.Wide.radix] at h
      omega
    refine WP.mono (VG.Proof.X448.Wide.tailStep_ok ts ho ho8 hk unpack hfalse t9 cap) fun u ⟨uc, uv, um, uk⟩ => ?_
    rw [te, tc] at uc uv
    refine ⟨?_, ?_, uc, (uk.1 _ (by decide)).trans tz, (uk.1 _ (by decide)).trans t9,
      tm.trans (um.mono (by omega) (by omega)), tk.trans (uk.mono (by decide))⟩
    · intro i hi
      by_cases h : i = k
      · subst i
        exact uv
      · have eq : VG.Proof.X448.Wide.coeff u.mem base o i = VG.Proof.X448.Wide.coeff t.mem base o i :=
          VG.Proof.X448.Wide.outside_coeff um (by omega) (by omega)
        rw [eq]
        exact tl i (by omega)
    · intro i hi hi'
      have sep : TMP + 16 * i + 16 ≤ o + 16 * k ∨ o + 16 * k + 16 ≤ TMP + 16 * i := by
        rcases hsep with h | h | h <;> omega
      have eq : VG.Proof.X448.Wide.coeff u.mem base TMP i = VG.Proof.X448.Wide.coeff t.mem base TMP i :=
        VG.Proof.X448.Wide.outside_coeff um sep (by simp only [TMP]; omega)
      rw [eq]
      exact th i (by omega) hi'
  rw [Impl.X448.AArch64.Tail.pass, WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Wide.passInit_ok s) fun u ⟨u6, uz, u9, um, uk⟩ => ?_
  refine WP.mono (wp_range_flatMap (M := isa) (N := 8) inv step 8 (by decide) u ?_)
    fun t ⟨tl, _, tc, _, _, tm, tk⟩ => ⟨tl, tc, tm, tk⟩
  refine ⟨fun _ hi => by omega, ?_, ?_, uz, u9, ?_, uk⟩
  · intro i _ hi; rw [um]; exact hf i hi
  · rw [u6]; rfl
  · rw [um]; exact Outside.refl _ _ _ _

end VG.Proof.X448.Wide

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Wide.TailNormalize`. -/
section

/-! Untrusted: normalize wide coefficients and restore the field-slot interface. -/
namespace VG.Proof.X448.Wide

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ACC TMP)
open VG.Impl.X448.AArch64.Wide VG.Proof.X448.AArch64

theorem tailNormalize_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat}
    (ho : o + 128 ≤ ACC) (ho8 : o % 8 = 0) {f : Nat → Nat}
    (hf : ∀ i < 8, VG.Proof.X448.Wide.coeff s.mem base TMP i = f i) (hb : ∀ i < 8, f i < 2 ^ 118) :
    WP isa (.block (Impl.X448.AArch64.Tail.normalize o)) s fun t =>
      (∀ i < 8, VG.Proof.X448.Wide.coeff t.mem base o i = VG.Proof.X448.Wide.encoded (VG.Proof.X448.Wide.normalized f i) true) ∧
      FieldMem base o s.mem t.mem ∧ Keeps VG.Proof.X448.Wide.colRegs s t := by
  have htmp : TMP + 128 ≤ 8192 := by decide
  have hwork : ∀ {m m' : Mem}, Outside base TMP 128 m m' → FieldMem base o m m' :=
    fun h => FieldMem.work h (by decide) (by decide)
  have keep : ∀ {a b : State}, Keeps [.x4] a b → Keeps VG.Proof.X448.Wide.colRegs a b :=
    fun h => h.mono (by decide)
  rw [Impl.X448.AArch64.Tail.normalize, List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Wide.pass_ok hs htmp (by decide) (Or.inl rfl) false hf hb) fun s₁ ⟨f₁, c₁, m₁, k₁⟩ => ?_
  simp only [VG.Proof.X448.Wide.encoded, Bool.false_eq_true, ite_false] at f₁
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Wide.fold_ok hs₁ f₁ c₁ (VG.Proof.X448.Wide.carry_bound hb)) fun s₂ ⟨f₂, m₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Wide.tailPass_ok hs₂ htmp (by decide) (Or.inl rfl) false (fun _ => rfl) f₂ (VG.Proof.X448.Wide.folded_small hb)) fun s₃ ⟨f₃, c₃, m₃, k₃⟩ => ?_
  simp only [VG.Proof.X448.Wide.encoded, Bool.false_eq_true, ite_false] at f₃
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Wide.fold_ok hs₃ f₃ c₃ (Nat.lt_trans (VG.Proof.X448.Wide.carry_small (VG.Proof.X448.Wide.folded_small hb)) (by decide))) fun s₄ ⟨f₄, m₄, k₄⟩ => ?_
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  refine WP.mono (VG.Proof.X448.Wide.tailPass_ok hs₄ (Nat.le_trans ho (by decide)) ho8
    (Or.inr (Or.inl (Nat.le_trans ho (by decide)))) true (by intro h; cases h) f₄
    (VG.Proof.X448.Wide.folded_small (VG.Proof.X448.Wide.folded_bound hb))) fun s₅ ⟨f₅, _, m₅, k₅⟩ => ?_
  exact ⟨f₅, (hwork m₁).trans ((hwork m₂).trans ((hwork m₃).trans ((hwork m₄).trans (.output m₅)))),
    k₁.trans ((keep k₂).trans (k₃.trans ((keep k₄).trans k₅)))⟩

end VG.Proof.X448.Wide

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Wide.TailProduct`. -/
section

/-! Untrusted: wide field multiplication behind the existing X448 slot contract. -/
namespace VG.Proof.X448.Wide

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ACC TMP)
open VG.Impl.X448.AArch64.Wide VG.Proof.X448.AArch64
open VG.Proof.X448 (toFe_mul)

theorem tailProduct_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat}
    (ho : VG.Proof.X448.AArch64.Slot o) (ho8 : o % 8 = 0) (ha : VG.Proof.X448.AArch64.Slot a) (ha8 : a % 8 = 0)
    (hb : VG.Proof.X448.AArch64.Slot b) (hb8 : b % 8 = 0) (ab : Bounded s.mem base a) (bb : Bounded s.mem base b) :
    WP isa (Impl.X448.AArch64.Tail.product o a b) s fun t =>
      VG.Proof.X448.AArch64.Op base o s t ∧ Bounded t.mem base o ∧ VG.Proof.X448.AArch64.F t.mem base o = VG.Proof.X448.AArch64.F s.mem base a * VG.Proof.X448.AArch64.F s.mem base b := by
  let f := VG.Proof.X448.Wide.paired (limbs s.mem base a)
  let g := VG.Proof.X448.Wide.paired (limbs s.mem base b)
  have fa : ∀ i < 8, f i < VG.Proof.X448.Wide.radix := VG.Proof.X448.Wide.paired_bound ab
  have gb : ∀ i < 8, g i < VG.Proof.X448.Wide.radix := VG.Proof.X448.Wide.paired_bound bb
  have aw : a + 128 ≤ 8192 := Nat.le_trans ha (by decide)
  have bw : b + 128 ≤ 8192 := Nat.le_trans hb (by decide)
  rw [Impl.X448.AArch64.Tail.product, List.append_assoc, List.append_assoc, List.append_assoc,
    WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Wide.pack_ok hs (o := PACKA) (by decide) aw (by decide) ha8
    (Or.inl (Nat.le_trans ha (by decide))) ab) fun s₁ ⟨a₁, m₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have b₁ : ∀ i < 16, limbs s₁.mem base b i = limbs s.mem base b i :=
    fun i hi => m₁.limbs (Or.inl (Nat.le_trans hb (by decide))) bw hi
  have bb₁ : Bounded s₁.mem base b := by
    intro i hi; rw [b₁ i hi]; exact bb i hi
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Wide.pack_ok hs₁ (o := PACKB) (by decide) bw (by decide) hb8
    (Or.inl (Nat.le_trans hb (by decide))) bb₁) fun s₂ ⟨b₂, m₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  have a₂ : ∀ i < 8, limbs s₂.mem base PACKA i = f i := by
    intro i hi
    have eq : limbs s₂.mem base PACKA i = limbs s₁.mem base PACKA i :=
      congrArg BitVec.toNat (m₂.word (by simp only [PACKA, PACKB]; omega) (by simp only [PACKA]; omega))
    rw [eq, a₁ i hi]
  have b₂' : ∀ i < 8, limbs s₂.mem base PACKB i = g i := by
    intro i hi
    rw [b₂ i hi]
    simp only [VG.Proof.X448.Wide.paired]
    rw [b₁ (2 * i) (by omega), b₁ (2 * i + 1) (by omega)]
    rfl
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Wide.columns_ok hs₂ (a := PACKA) (b := PACKB) (Or.inr (by decide))
    (Or.inr (by decide)) (by decide) (by decide) (by decide) (by decide)
    (by intro i hi; rw [a₂ i hi]; exact fa i hi)
    (by intro i hi; rw [b₂' i hi]; exact gb i hi)) fun s₃ ⟨c₃, m₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  have c₃' : ∀ i < 16, VG.Proof.X448.Wide.coeff s₃.mem base ACC i = VG.Proof.X448.Wide.rows f g 8 i := by
    intro i hi
    rw [c₃ i hi]
    exact VG.Proof.X448.Wide.rows_congr a₂ b₂' (by decide) i
  have raw : ∀ i < 16, VG.Proof.X448.Wide.coeff s₃.mem base ACC i < 2 ^ 116 := by
    intro i hi
    rw [c₃' i hi]
    exact Nat.lt_of_le_of_lt (VG.Proof.X448.Wide.rows_bound fa gb (by decide) i) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Wide.reduce_ok hs₃ raw) fun s₄ ⟨r₄, m₄, k₄⟩ => ?_
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  have red := VG.Proof.X448.Wide.reduced_bound raw
  refine WP.mono (VG.Proof.X448.Wide.tailNormalize_ok hs₄ ho ho8 r₄ red) fun t ⟨tf, tm, tk⟩ => ?_
  have out := VG.Proof.X448.Wide.encoded_limbs tf
  have val : VG.Proof.X448.AArch64.fe t.mem base o % Spec.X448.P =
      (VG.Proof.X448.AArch64.fe s.mem base a * VG.Proof.X448.AArch64.fe s.mem base b) % Spec.X448.P := by
    rw [show VG.Proof.X448.AArch64.fe t.mem base o = VG.Proof.X448.valN
        (VG.Proof.X448.Wide.unpacked (VG.Proof.X448.Wide.normalized (VG.Proof.X448.Wide.reduced (VG.Proof.X448.Wide.coeff s₃.mem base ACC)))) 16 from
        VG.Proof.X448.valN_congr out,
      VG.Proof.X448.Wide.unpacked_val, VG.Proof.X448.Wide.normalized_mod red, VG.Proof.X448.Wide.reduced_mod,
      VG.Proof.X448.Wide.valN_congr c₃', VG.Proof.X448.Wide.rows_val f g (by decide), VG.Proof.X448.Wide.paired_val, VG.Proof.X448.Wide.paired_val]
  refine ⟨⟨?_, ?_⟩, ?_, VG.Proof.X448.toFe_mul val⟩
  · exact (k₁.mono (by decide)).trans ((k₂.mono (by decide)).trans
      ((k₃.mono (by decide)).trans ((k₄.mono (by decide)).trans (tk.mono (by decide)))))
  · exact (FieldMem.work m₁ (by decide) (by decide)).trans
      ((FieldMem.work m₂ (by decide) (by decide)).trans
      ((FieldMem.work m₃ (by decide) (by decide)).trans
      ((FieldMem.work m₄ (by decide) (by decide)).trans tm)))
  · intro i hi
    rw [out i hi]
    exact VG.Proof.X448.Wide.unpacked_bound (fun j _ => VG.Proof.X448.Wide.digit_lt _ j) i hi

end VG.Proof.X448.Wide

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Wide.TailSquare`. -/
section

/-! Untrusted: cached-input squaring behind the unchanged field-slot contract. -/
namespace VG.Proof.X448.Wide

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ACC)
open VG.Impl.X448.AArch64.Cached VG.Proof.X448.AArch64
open VG.Proof.X448 (toFe_mul)

theorem tailSquare_ok {s : State} {base : Addr} (hs : Scr s base) {o a : Nat}
    (ho : VG.Proof.X448.AArch64.Slot o) (ho8 : o % 8 = 0) (ha : VG.Proof.X448.AArch64.Slot a) (ha8 : a % 8 = 0) (ab : Bounded s.mem base a) :
    WP isa (Impl.X448.AArch64.Tail.sqr o a) s fun t =>
      VG.Proof.X448.AArch64.Op base o s t ∧ Bounded t.mem base o ∧ VG.Proof.X448.AArch64.F t.mem base o = VG.Proof.X448.AArch64.F s.mem base a * VG.Proof.X448.AArch64.F s.mem base a := by
  let f := VG.Proof.X448.Wide.paired (limbs s.mem base a)
  have fb : ∀ i < 8, f i < VG.Proof.X448.Wide.radix := VG.Proof.X448.Wide.paired_bound ab
  rw [Impl.X448.AArch64.Tail.sqr, List.append_assoc, List.append_assoc, List.append_assoc,
    WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Wide.pack_ok hs (o := Impl.X448.AArch64.Wide.PACKA) (by decide)
    (Nat.le_trans ha (by decide)) (by decide) ha8 (Or.inl (Nat.le_trans ha (by decide))) ab)
    fun s₁ ⟨a₁, m₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Wide.loadCached_ok hs₁ (a := Impl.X448.AArch64.Wide.PACKA) (by decide) (by decide))
    fun s₂ ⟨c₂, m₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  have fc : ∀ i < 8, (s₂.gpr (cacheReg i)).toNat = f i := by
    intro i hi
    rw [c₂ i hi]
    exact a₁ i hi
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Wide.symmetricColumns_ok hs₂ fc fb) fun s₃ ⟨c₃, m₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  have raw : ∀ i < 16, VG.Proof.X448.Wide.coeff s₃.mem base ACC i < 2 ^ 116 := by
    intro i hi
    rw [c₃ i hi]
    exact Nat.lt_of_le_of_lt (VG.Proof.X448.Wide.rows_bound fb fb (by decide) i) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Wide.reduce_ok hs₃ raw) fun s₄ ⟨r₄, m₄, k₄⟩ => ?_
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  have red := VG.Proof.X448.Wide.reduced_bound raw
  refine WP.mono (VG.Proof.X448.Wide.tailNormalize_ok hs₄ ho ho8 r₄ red) fun t ⟨tf, tm, tk⟩ => ?_
  have out := VG.Proof.X448.Wide.encoded_limbs tf
  have val : VG.Proof.X448.AArch64.fe t.mem base o % Spec.X448.P =
      (VG.Proof.X448.AArch64.fe s.mem base a * VG.Proof.X448.AArch64.fe s.mem base a) % Spec.X448.P := by
    rw [show VG.Proof.X448.AArch64.fe t.mem base o = VG.Proof.X448.valN
        (VG.Proof.X448.Wide.unpacked (VG.Proof.X448.Wide.normalized (VG.Proof.X448.Wide.reduced (VG.Proof.X448.Wide.coeff s₃.mem base ACC)))) 16 from
        VG.Proof.X448.valN_congr out,
      VG.Proof.X448.Wide.unpacked_val, VG.Proof.X448.Wide.normalized_mod red, VG.Proof.X448.Wide.reduced_mod,
      VG.Proof.X448.Wide.valN_congr c₃, VG.Proof.X448.Wide.rows_val f f (by decide), VG.Proof.X448.Wide.paired_val]
  refine ⟨⟨?_, ?_⟩, ?_, VG.Proof.X448.toFe_mul val⟩
  · exact (k₁.mono (by decide)).trans ((k₂.mono (by decide)).trans
      ((k₃.mono (by decide)).trans ((k₄.mono (by decide)).trans (tk.mono (by decide)))))
  · rw [m₂] at m₃
    exact (FieldMem.work m₁ (by decide) (by decide)).trans
      ((FieldMem.work m₃ (by decide) (by decide)).trans
      ((FieldMem.work m₄ (by decide) (by decide)).trans tm))
  · intro i hi
    rw [out i hi]
    exact VG.Proof.X448.Wide.unpacked_bound (fun j _ => VG.Proof.X448.Wide.digit_lt _ j) i hi

end VG.Proof.X448.Wide

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Wide.TailMul`. -/
section

/-! Untrusted: choose cached squaring from public, static field-slot indices. -/
namespace VG.Proof.X448.Wide

open VG VG.AArch64 VG.Proof.X448.AArch64

theorem tailMul_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat}
    (ho : VG.Proof.X448.AArch64.Slot o) (ho8 : o % 8 = 0) (ha : VG.Proof.X448.AArch64.Slot a) (ha8 : a % 8 = 0)
    (hb : VG.Proof.X448.AArch64.Slot b) (hb8 : b % 8 = 0) (ab : Bounded s.mem base a) (bb : Bounded s.mem base b) :
    WP isa (Impl.X448.AArch64.Tail.mul o a b) s fun t =>
      VG.Proof.X448.AArch64.Op base o s t ∧ Bounded t.mem base o ∧ VG.Proof.X448.AArch64.F t.mem base o = VG.Proof.X448.AArch64.F s.mem base a * VG.Proof.X448.AArch64.F s.mem base b := by
  rw [Impl.X448.AArch64.Tail.mul]
  by_cases h : a = b
  · rw [ite_eq_left h, ← h]
    exact VG.Proof.X448.Wide.tailSquare_ok hs ho ho8 ha ha8 ab
  · rw [ite_eq_right h]
    exact VG.Proof.X448.Wide.tailProduct_ok hs ho ho8 ha ha8 hb hb8 ab bb

end VG.Proof.X448.Wide

end
