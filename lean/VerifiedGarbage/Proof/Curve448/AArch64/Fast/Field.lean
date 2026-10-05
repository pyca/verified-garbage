import VerifiedGarbage.Proof.X448.Wide.TailMul
import VerifiedGarbage.Impl.Curve448.AArch64.Fast
import VerifiedGarbage.Proof.X448.AArch64.PointwiseSmall
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.X448.AArch64.Main
import VerifiedGarbage.Proof.X448.Encoding

/- Proofs formerly in `VerifiedGarbage.Proof.Curve448.AArch64.Fast.Carry`. -/
section

/-!
# Carrying a product's coefficients

Untrusted: everything here is checked by Lean. Coefficients `0`–`3` carry
into each other and into `4`, and `4`–`7` into each other and, by
`2⁴⁴⁸ = 2²²⁴ + 1 (mod p)`, into `0` and `4`; one more carry from `0` and `4`
into `1` and `5` leaves limbs within `2⁵⁶ + 2⁸`. `out` describes the limbs,
`out_val` their value.
-/

namespace VG.Proof.Curve448.AArch64.Fast

open VG.Spec.X448
open VG.Proof.X448.Wide (valN valN_succ radix half full)

/-- The carry into coefficient `lo + n` of the chain from `lo`. -/
def chain (r : Nat → Nat) (lo : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => (r (lo + n) + VG.Proof.Curve448.AArch64.Fast.chain r lo n) / VG.Proof.X448.Wide.radix

/-- Limb `lo + n` of the chain from `lo`. -/
def chainLimb (r : Nat → Nat) (lo n : Nat) : Nat := (r (lo + n) + VG.Proof.Curve448.AArch64.Fast.chain r lo n) % VG.Proof.X448.Wide.radix

/-- The limbs after both chains and the final carries. -/
def out (r : Nat → Nat) (i : Nat) : Nat :=
  let c₀ := VG.Proof.Curve448.AArch64.Fast.chainLimb r 0 0 + VG.Proof.Curve448.AArch64.Fast.chain r 4 4
  let c₄ := VG.Proof.Curve448.AArch64.Fast.chainLimb r 4 0 + VG.Proof.Curve448.AArch64.Fast.chain r 0 4 + VG.Proof.Curve448.AArch64.Fast.chain r 4 4
  match i with
  | 0 => c₀ % VG.Proof.X448.Wide.radix
  | 1 => VG.Proof.Curve448.AArch64.Fast.chainLimb r 0 1 + c₀ / VG.Proof.X448.Wide.radix
  | 2 => VG.Proof.Curve448.AArch64.Fast.chainLimb r 0 2
  | 3 => VG.Proof.Curve448.AArch64.Fast.chainLimb r 0 3
  | 4 => c₄ % VG.Proof.X448.Wide.radix
  | 5 => VG.Proof.Curve448.AArch64.Fast.chainLimb r 4 1 + c₄ / VG.Proof.X448.Wide.radix
  | 6 => VG.Proof.Curve448.AArch64.Fast.chainLimb r 4 2
  | _ => VG.Proof.Curve448.AArch64.Fast.chainLimb r 4 3

theorem chain_val (r : Nat → Nat) (lo n : Nat) :
    VG.Proof.X448.Wide.valN (fun k => VG.Proof.Curve448.AArch64.Fast.chainLimb r lo k) n + VG.Proof.X448.Wide.radix ^ n * VG.Proof.Curve448.AArch64.Fast.chain r lo n = VG.Proof.X448.Wide.valN (fun k => r (lo + k)) n := by
  induction n with
  | zero => simp only [VG.Proof.X448.Wide.valN, VG.Proof.Curve448.AArch64.Fast.chain, Nat.mul_zero, Nat.add_zero]
  | succ n ih =>
    have hd := Nat.mod_add_div (r (lo + n) + VG.Proof.Curve448.AArch64.Fast.chain r lo n) VG.Proof.X448.Wide.radix
    simp only [VG.Proof.X448.Wide.valN_succ, VG.Proof.Curve448.AArch64.Fast.chain, VG.Proof.Curve448.AArch64.Fast.chainLimb] at hd ih ⊢
    rw [Nat.pow_succ, ← ih]
    generalize VG.Proof.X448.Wide.radix ^ n = X at *
    have : X * ((r (lo + n) + VG.Proof.Curve448.AArch64.Fast.chain r lo n) % VG.Proof.X448.Wide.radix) +
        X * VG.Proof.X448.Wide.radix * ((r (lo + n) + VG.Proof.Curve448.AArch64.Fast.chain r lo n) / VG.Proof.X448.Wide.radix) =
        X * r (lo + n) + X * VG.Proof.Curve448.AArch64.Fast.chain r lo n := by
      rw [Nat.mul_assoc, ← Nat.mul_add, hd, Nat.mul_add]
    rw [Nat.add_assoc, this]
    ac_rfl

theorem out_val (r : Nat → Nat) :
    VG.Proof.X448.Wide.valN (VG.Proof.Curve448.AArch64.Fast.out r) 8 + VG.Spec.X448.P * VG.Proof.Curve448.AArch64.Fast.chain r 4 4 = VG.Proof.X448.Wide.valN r 8 := by
  have hl := VG.Proof.Curve448.AArch64.Fast.chain_val r 0 4
  have hh := VG.Proof.Curve448.AArch64.Fast.chain_val r 4 4
  have h0 := Nat.mod_add_div (VG.Proof.Curve448.AArch64.Fast.chainLimb r 0 0 + VG.Proof.Curve448.AArch64.Fast.chain r 4 4) VG.Proof.X448.Wide.radix
  have h4 := Nat.mod_add_div (VG.Proof.Curve448.AArch64.Fast.chainLimb r 4 0 + VG.Proof.Curve448.AArch64.Fast.chain r 0 4 + VG.Proof.Curve448.AArch64.Fast.chain r 4 4) VG.Proof.X448.Wide.radix
  have hp : VG.Spec.X448.P = VG.Proof.X448.Wide.radix ^ 8 - VG.Proof.X448.Wide.radix ^ 4 - 1 := by decide +kernel
  simp only [VG.Proof.X448.Wide.valN, VG.Proof.Curve448.AArch64.Fast.out, Nat.zero_add, Nat.add_zero, Nat.reduceAdd, Nat.pow_zero, Nat.one_mul] at hl hh ⊢
  simp only [hp, VG.Proof.X448.Wide.radix, Nat.reducePow] at hl hh h0 h4 ⊢
  omega

/-- The value modulo `p`. -/
theorem out_mod (r : Nat → Nat) : VG.Proof.X448.Wide.valN (VG.Proof.Curve448.AArch64.Fast.out r) 8 % VG.Spec.X448.P = VG.Proof.X448.Wide.valN r 8 % VG.Spec.X448.P := by
  rw [← VG.Proof.Curve448.AArch64.Fast.out_val r, Nat.add_mul_mod_self_left]

end VG.Proof.Curve448.AArch64.Fast

end

/- Proofs formerly in `VerifiedGarbage.Proof.Curve448.AArch64.Fast.Bounds`. -/
section

/-!
# Bounds of a product's coefficients and carries

Untrusted: everything here is checked by Lean. Operand limbs below `Ib`
(sums and differences of reduced elements) give coefficients below `2¹²⁰`,
carries of one word, and limbs of the result below `Mb`.
-/

namespace VG.Proof.Curve448.AArch64.Fast

open VG.Proof.X448.Wide (rows reduced addRow_at radix)

/-- The bound of a reduced element's limbs. -/
def Mb : Nat := 2 ^ 56 + 2 ^ 8

/-- The bound of a multiplication's operand limbs. -/
def Ib : Nat := 3 * 2 ^ 56 + 2 ^ 9

/-- The number of products in a schoolbook coefficient. -/
def cnt (k : Nat) : Nat := ((List.range 8).filter fun n => n ≤ k ∧ k < n + 8).length

theorem rows_le {f g : Nat → Nat} {B : Nat} (hf : ∀ i < 8, f i ≤ B) (hg : ∀ i < 8, g i ≤ B)
    (k : Nat) : VG.Proof.X448.Wide.rows f g 8 k ≤ VG.Proof.Curve448.AArch64.Fast.cnt k * (B * B) := by
  have : ∀ n ≤ 8, VG.Proof.X448.Wide.rows f g n k ≤ ((List.range n).filter fun m => m ≤ k ∧ k < m + 8).length * (B * B) := by
    intro n hn
    induction n with
    | zero => simp [VG.Proof.X448.Wide.rows]
    | succ n ih =>
      rw [VG.Proof.X448.Wide.rows, VG.Proof.X448.Wide.addRow_at, List.range_succ, List.filter_append, List.length_append]
      have := ih (by omega)
      split
      · rename_i h
        have hp : f n * g (k - n) ≤ B * B :=
          Nat.mul_le_mul (hf n (by omega)) (hg (k - n) (by omega))
        simp only [List.filter_cons, List.filter_nil, decide_eq_true h, ite_true,
          List.length_singleton, Nat.add_mul, Nat.one_mul]
        omega
      · rename_i h
        simp only [List.filter_cons, List.filter_nil, decide_eq_false h, Bool.false_eq_true,
          ite_false, List.length_nil, Nat.add_zero]
        omega
  exact this 8 (Nat.le_refl _)

/-- The number of products in coefficient `k` of a reduced product. -/
def rc (k : Nat) : Nat := VG.Proof.Curve448.AArch64.Fast.cnt k + VG.Proof.Curve448.AArch64.Fast.cnt (k + 8) + if k < 4 then VG.Proof.Curve448.AArch64.Fast.cnt (k + 12) else VG.Proof.Curve448.AArch64.Fast.cnt (k + 4) + VG.Proof.Curve448.AArch64.Fast.cnt (k + 8)

theorem rc_eq : VG.Proof.Curve448.AArch64.Fast.rc 0 = 11 ∧ VG.Proof.Curve448.AArch64.Fast.rc 1 = 10 ∧ VG.Proof.Curve448.AArch64.Fast.rc 2 = 9 ∧ VG.Proof.Curve448.AArch64.Fast.rc 3 = 8 ∧ VG.Proof.Curve448.AArch64.Fast.rc 4 = 18 ∧ VG.Proof.Curve448.AArch64.Fast.rc 5 = 16 ∧ VG.Proof.Curve448.AArch64.Fast.rc 6 = 14 ∧
    VG.Proof.Curve448.AArch64.Fast.rc 7 = 12 := by decide

theorem reduced_le {f g : Nat → Nat} {B : Nat} (hf : ∀ i < 8, f i ≤ B) (hg : ∀ i < 8, g i ≤ B)
    (k : Nat) : VG.Proof.X448.Wide.reduced (VG.Proof.X448.Wide.rows f g 8) k ≤ VG.Proof.Curve448.AArch64.Fast.rc k * (B * B) := by
  have r := VG.Proof.Curve448.AArch64.Fast.rows_le hf hg
  simp only [VG.Proof.X448.Wide.reduced, VG.Proof.Curve448.AArch64.Fast.rc]
  split
  · have := r k; have := r (k + 8); have := r (k + 12)
    rw [Nat.add_mul, Nat.add_mul]; omega
  · have := r k; have := r (k + 8); have := r (k + 4)
    rw [Nat.add_mul, Nat.add_mul, Nat.add_mul]; omega

/-- What the code needs of a product's coefficients. -/
structure Fits (r : Nat → Nat) : Prop where
  low : ∀ n < 4, r n + VG.Proof.Curve448.AArch64.Fast.chain r 0 n < 2 ^ 120
  high : ∀ n < 4, r (4 + n) + VG.Proof.Curve448.AArch64.Fast.chain r 4 n < 2 ^ 120
  c₀ : VG.Proof.Curve448.AArch64.Fast.chainLimb r 0 0 + VG.Proof.Curve448.AArch64.Fast.chain r 4 4 < 2 ^ 64
  c₄ : VG.Proof.Curve448.AArch64.Fast.chainLimb r 4 0 + VG.Proof.Curve448.AArch64.Fast.chain r 0 4 + VG.Proof.Curve448.AArch64.Fast.chain r 4 4 < 2 ^ 64
  out : ∀ i < 8, VG.Proof.Curve448.AArch64.Fast.out r i < VG.Proof.Curve448.AArch64.Fast.Mb

theorem fits {r : Nat → Nat} (h : ∀ k < 8, r k ≤ VG.Proof.Curve448.AArch64.Fast.rc k * ((VG.Proof.Curve448.AArch64.Fast.Ib - 1) * (VG.Proof.Curve448.AArch64.Fast.Ib - 1))) : VG.Proof.Curve448.AArch64.Fast.Fits r := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ := VG.Proof.Curve448.AArch64.Fast.rc_eq
  have h0 := h 0 (by decide); have h1 := h 1 (by decide); have h2 := h 2 (by decide)
  have h3 := h 3 (by decide); have h4 := h 4 (by decide); have h5 := h 5 (by decide)
  have h6 := h 6 (by decide); have h7 := h 7 (by decide)
  rw [e0] at h0; rw [e1] at h1; rw [e2] at h2; rw [e3] at h3
  rw [e4] at h4; rw [e5] at h5; rw [e6] at h6; rw [e7] at h7
  simp only [VG.Proof.Curve448.AArch64.Fast.Ib, Nat.reducePow, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] at h0 h1 h2 h3 h4 h5 h6 h7
  have l1 : VG.Proof.Curve448.AArch64.Fast.chain r 0 1 = r 0 / VG.Proof.X448.Wide.radix := by simp [VG.Proof.Curve448.AArch64.Fast.chain]
  have l2 : VG.Proof.Curve448.AArch64.Fast.chain r 0 2 = (r 1 + VG.Proof.Curve448.AArch64.Fast.chain r 0 1) / VG.Proof.X448.Wide.radix := by simp [VG.Proof.Curve448.AArch64.Fast.chain]
  have l3 : VG.Proof.Curve448.AArch64.Fast.chain r 0 3 = (r 2 + VG.Proof.Curve448.AArch64.Fast.chain r 0 2) / VG.Proof.X448.Wide.radix := by simp [VG.Proof.Curve448.AArch64.Fast.chain]
  have l4 : VG.Proof.Curve448.AArch64.Fast.chain r 0 4 = (r 3 + VG.Proof.Curve448.AArch64.Fast.chain r 0 3) / VG.Proof.X448.Wide.radix := by simp [VG.Proof.Curve448.AArch64.Fast.chain]
  have m1 : VG.Proof.Curve448.AArch64.Fast.chain r 4 1 = r 4 / VG.Proof.X448.Wide.radix := by simp [VG.Proof.Curve448.AArch64.Fast.chain]
  have m2 : VG.Proof.Curve448.AArch64.Fast.chain r 4 2 = (r 5 + VG.Proof.Curve448.AArch64.Fast.chain r 4 1) / VG.Proof.X448.Wide.radix := by simp [VG.Proof.Curve448.AArch64.Fast.chain]
  have m3 : VG.Proof.Curve448.AArch64.Fast.chain r 4 3 = (r 6 + VG.Proof.Curve448.AArch64.Fast.chain r 4 2) / VG.Proof.X448.Wide.radix := by simp [VG.Proof.Curve448.AArch64.Fast.chain]
  have m4 : VG.Proof.Curve448.AArch64.Fast.chain r 4 4 = (r 7 + VG.Proof.Curve448.AArch64.Fast.chain r 4 3) / VG.Proof.X448.Wide.radix := by simp [VG.Proof.Curve448.AArch64.Fast.chain]
  have z0 : VG.Proof.Curve448.AArch64.Fast.chain r 0 0 = 0 := rfl
  have y0 : VG.Proof.Curve448.AArch64.Fast.chain r 4 0 = 0 := rfl
  simp only [VG.Proof.X448.Wide.radix, Nat.reducePow] at l1 l2 l3 l4 m1 m2 m3 m4
  have k00 : VG.Proof.Curve448.AArch64.Fast.chainLimb r 0 0 < 2 ^ 56 := Nat.mod_lt _ (by decide)
  have k01 : VG.Proof.Curve448.AArch64.Fast.chainLimb r 0 1 < 2 ^ 56 := Nat.mod_lt _ (by decide)
  have k02 : VG.Proof.Curve448.AArch64.Fast.chainLimb r 0 2 < 2 ^ 56 := Nat.mod_lt _ (by decide)
  have k03 : VG.Proof.Curve448.AArch64.Fast.chainLimb r 0 3 < 2 ^ 56 := Nat.mod_lt _ (by decide)
  have k40 : VG.Proof.Curve448.AArch64.Fast.chainLimb r 4 0 < 2 ^ 56 := Nat.mod_lt _ (by decide)
  have k41 : VG.Proof.Curve448.AArch64.Fast.chainLimb r 4 1 < 2 ^ 56 := Nat.mod_lt _ (by decide)
  have k42 : VG.Proof.Curve448.AArch64.Fast.chainLimb r 4 2 < 2 ^ 56 := Nat.mod_lt _ (by decide)
  have k43 : VG.Proof.Curve448.AArch64.Fast.chainLimb r 4 3 < 2 ^ 56 := Nat.mod_lt _ (by decide)
  refine ⟨fun n hn => ?_, fun n hn => ?_, by omega, by omega, fun i hi => ?_⟩
  · obtain rfl | rfl | rfl | rfl : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
    all_goals omega
  · obtain rfl | rfl | rfl | rfl : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
    all_goals simp only [Nat.reduceAdd]; omega
  · simp only [VG.Proof.Curve448.AArch64.Fast.Mb]
    obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
        i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
    all_goals simp only [VG.Proof.Curve448.AArch64.Fast.out, VG.Proof.X448.Wide.radix, Nat.reducePow]; omega

end VG.Proof.Curve448.AArch64.Fast

end

/- Proofs formerly in `VerifiedGarbage.Proof.Curve448.AArch64.Fast.Word`. -/
section

/-!
# Two-word accumulators modulo 2¹²⁸

Untrusted: everything here is checked by Lean. A pair of words added to or
subtracted from another pair, with the carry, is the sum or difference
modulo `2 ^ 128`. A product's coefficient can be accumulated with
subtractions as well as additions this way: it is exact once the true value
is known to be in `[0, 2 ^ 128)`.
-/

namespace VG.Proof.Curve448.AArch64.Fast

open VG VG.AArch64 VG.Proof.Ed25519.Word64
open VG.Proof.X448.Wide (pair)
open VG.Proof.Ed25519.AArch64 (mulHi mul_lo_hi)

abbrev M : Nat := 2 ^ 128

theorem pair_lt (lo hi : BitVec 64) : VG.Proof.X448.Wide.pair lo hi < VG.Proof.Curve448.AArch64.Fast.M := by
  have := lo.isLt; have := hi.isLt
  simp only [VG.Proof.X448.Wide.pair, VG.Proof.Curve448.AArch64.Fast.M]
  omega

theorem addPair_mod (lo hi a b : BitVec 64) :
    VG.Proof.X448.Wide.pair (addCarry lo a false) (addCarry hi b (carryOut lo a false)) = (VG.Proof.X448.Wide.pair lo hi + VG.Proof.X448.Wide.pair a b) % VG.Proof.Curve448.AArch64.Fast.M := by
  have e0 := addCarry_value lo a false
  have e1 := addCarry_value hi b (carryOut lo a false)
  have h := VG.Proof.Curve448.AArch64.Fast.pair_lt (addCarry lo a false) (addCarry hi b (carryOut lo a false))
  have hc := Bool.toNat_le (carryOut hi b (carryOut lo a false))
  simp only [Bool.toNat_false, Nat.add_zero] at e0
  simp only [VG.Proof.X448.Wide.pair, VG.Proof.Curve448.AArch64.Fast.M] at h ⊢
  omega

theorem subPair_mod (lo hi a b : BitVec 64) :
    VG.Proof.X448.Wide.pair (addCarry lo (~~~a) true) (addCarry hi (~~~b) (carryOut lo (~~~a) true)) =
      (VG.Proof.X448.Wide.pair lo hi + (VG.Proof.Curve448.AArch64.Fast.M - VG.Proof.X448.Wide.pair a b)) % VG.Proof.Curve448.AArch64.Fast.M := by
  have e0 := addCarry_value lo (~~~a) true
  have e1 := addCarry_value hi (~~~b) (carryOut lo (~~~a) true)
  have h := VG.Proof.Curve448.AArch64.Fast.pair_lt (addCarry lo (~~~a) true) (addCarry hi (~~~b) (carryOut lo (~~~a) true))
  have hc := Bool.toNat_le (carryOut hi (~~~b) (carryOut lo (~~~a) true))
  have ha := a.isLt; have hb := b.isLt
  simp only [BitVec.toNat_not, Bool.toNat_true] at e0 e1
  simp only [VG.Proof.X448.Wide.pair, VG.Proof.Curve448.AArch64.Fast.M] at h ⊢
  omega

theorem mulPair (a b : BitVec 64) : VG.Proof.X448.Wide.pair (a * b) (mulHi a b) = a.toNat * b.toNat := by
  have := mul_lo_hi a b
  simp only [VG.Proof.X448.Wide.pair]
  omega

/-- Adding to an accumulator, as integers modulo `2 ^ 128`. -/
theorem add_emod {x : Nat} {e : Int} (h : (x : Int) = e % VG.Proof.Curve448.AArch64.Fast.M) (p : Nat) :
    (((x + p) % VG.Proof.Curve448.AArch64.Fast.M : Nat) : Int) = (e + p) % VG.Proof.Curve448.AArch64.Fast.M := by
  rw [Int.natCast_emod, Int.natCast_add, h, Int.emod_add_emod]

/-- Subtracting from an accumulator, as integers modulo `2 ^ 128`. -/
theorem sub_emod {x : Nat} {e : Int} (h : (x : Int) = e % VG.Proof.Curve448.AArch64.Fast.M) {p : Nat} (hp : p ≤ VG.Proof.Curve448.AArch64.Fast.M) :
    (((x + (VG.Proof.Curve448.AArch64.Fast.M - p)) % VG.Proof.Curve448.AArch64.Fast.M : Nat) : Int) = (e - p) % VG.Proof.Curve448.AArch64.Fast.M := by
  rw [Int.natCast_emod, Int.natCast_add, Int.natCast_sub hp, h, Int.emod_add_emod,
    show e + ((VG.Proof.Curve448.AArch64.Fast.M : Nat) - (p : Int)) = e - p + (VG.Proof.Curve448.AArch64.Fast.M : Nat) by omega, Int.add_emod_right]

/-- An accumulator holds its true value once that is known to fit. -/
theorem exact_of_emod {x : Nat} {e : Int} (h : (x : Int) = e % VG.Proof.Curve448.AArch64.Fast.M) {v : Nat} (hv : e = v)
    (hlt : v < VG.Proof.Curve448.AArch64.Fast.M) : x = v := by
  rw [hv, ← Int.natCast_emod, Nat.mod_eq_of_lt hlt] at h
  exact Int.ofNat.inj h

end VG.Proof.Curve448.AArch64.Fast

end

/- Proofs formerly in `VerifiedGarbage.Proof.Curve448.AArch64.Fast.MOp`. -/
section

/-!
# Product accumulation, for any list of steps

Untrusted: everything here is checked by Lean. `mops_ok`: running the code
of a list of `MOp`s leaves in each accumulator, modulo `2 ^ 128`, the signed
sum of products that `sem` computes from the multiplicands' values in the
initial state. The registers are checked once (`Good`, by `decide`): the
temporaries and accumulators are distinct, and no multiplicand is one of them
(`MOp.ok`).
-/

namespace VG.Proof.Curve448.AArch64.Fast

open VG VG.AArch64 VG.Proof.Ed25519.Word64
open VG.Impl.Curve448.AArch64.Fast
open VG.Impl.X448.AArch64 (ld)
open VG.Proof.X448.Wide (pair)
open VG.Proof.X448.AArch64 (Keeps Scr word off load_sc addr_word read8_eq)
open VG.Proof.Ed25519.AArch64 (mulHi read_x)

/-- The value of an accumulator. -/
def accVal (s : State) (a : Acc) : Nat := VG.Proof.X448.Wide.pair (s.gpr a.lo) (s.gpr a.hi)

/-- The value of a multiplicand, for the second operand at `b`. -/
def srcVal (s : State) (base : Addr) (b : Nat) : Src → Nat
  | .reg r => (s.gpr r).toNat
  | .mem d => (word s.mem base d).toNat
  | .arg k => (word s.mem base (b + 8 * k)).toNat

abbrev Env := Acc → Int

def upd (e : VG.Proof.Curve448.AArch64.Fast.Env) (a : Acc) (v : Int) : VG.Proof.Curve448.AArch64.Fast.Env := fun c => if c = a then v else e c

/-- One target of a product `p`. -/
def target (p : Int) (e : VG.Proof.Curve448.AArch64.Fast.Env) (t : Acc × Bool) : VG.Proof.Curve448.AArch64.Fast.Env :=
  VG.Proof.Curve448.AArch64.Fast.upd e t.1 (if t.2 then e t.1 + p else e t.1 - p)

def opSem (v : Src → Nat) (e : VG.Proof.Curve448.AArch64.Fast.Env) : MOp → VG.Proof.Curve448.AArch64.Fast.Env
  | .set a x y => VG.Proof.Curve448.AArch64.Fast.upd e a (v x * v y)
  | .prod x y ts => ts.foldl (VG.Proof.Curve448.AArch64.Fast.target (v x * v y)) e
  | .merge d s add => VG.Proof.Curve448.AArch64.Fast.upd e d (if add then e d + e s else e d - e s)

/-- The accumulators after a list of steps. -/
def sem (v : Src → Nat) : VG.Proof.Curve448.AArch64.Fast.Env → List MOp → VG.Proof.Curve448.AArch64.Fast.Env
  | e, [] => e
  | e, op :: ops => VG.Proof.Curve448.AArch64.Fast.sem v (VG.Proof.Curve448.AArch64.Fast.opSem v e op) ops

/-! ## Well-formedness, by `decide` -/

def accRegs (accs : List Acc) : List Reg := accs.flatMap fun a => [a.lo, a.hi]

/-- The registers the steps may write. -/
def writes (R : Regs) (accs : List Acc) : List Reg := R.t :: R.p0 :: R.p1 :: VG.Proof.Curve448.AArch64.Fast.accRegs accs

/-- Distinct temporaries and accumulators, other than `x3` and `x12`. -/
abbrev Good (R : Regs) (accs : List Acc) : Prop :=
  R.t ≠ R.p0 ∧ R.t ≠ R.p1 ∧ R.p0 ≠ R.p1 ∧
  (∀ a ∈ accs, a.lo ≠ a.hi ∧ a.lo ∉ [R.t, R.p0, R.p1] ∧ a.hi ∉ [R.t, R.p0, R.p1]) ∧
  (∀ a ∈ accs, ∀ c ∈ accs, a ≠ c → a.lo ∉ [c.lo, c.hi] ∧ a.hi ∉ [c.lo, c.hi]) ∧
  .x3 ∉ VG.Proof.Curve448.AArch64.Fast.writes R accs ∧ .x12 ∉ VG.Proof.Curve448.AArch64.Fast.writes R accs

def srcOk (W : List Reg) : Src → Bool
  | .reg r => !W.contains r
  | .mem d => d % 8 == 0 && d + 8 ≤ 8192
  | .arg k => k < 8

def opOk (W : List Reg) (accs : List Acc) : MOp → Bool
  | .set a x y => accs.contains a && VG.Proof.Curve448.AArch64.Fast.srcOk W x && VG.Proof.Curve448.AArch64.Fast.srcOk W y
  | .prod x y ts => VG.Proof.Curve448.AArch64.Fast.srcOk W x && VG.Proof.Curve448.AArch64.Fast.srcOk W y && ts.all (fun t => accs.contains t.1)
  | .merge d s _ => accs.contains d && accs.contains s && d != s

/-! ## The instructions -/

theorem ld_ok {s : State} {base : Addr} (hs : Scr s base) (r : Reg) {d : Nat}
    (h8 : d % 8 = 0) (hd : d + 8 ≤ 8192) :
    WP isa (.block [ld r d]) s fun t =>
      t.gpr r = word s.mem base d ∧ t.mem = s.mem ∧ Keeps [r] s t := by
  have l := hs.read (d := d) (n := 8) hd
  have ae : d % 8 = 0 ∧ d < 32768 := ⟨h8, by omega⟩
  refine WP.of_runBlock ⟨_, by
    simp only [ld, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
      State.load, ae, and_self, hs.x3, l, ite_true, Option.map_some, Option.bind_some]; rfl, ?_⟩
  refine ⟨?_, rfl, fun q hq => ?_, rfl, rfl⟩
  · rw [RegUpd.gpr_write_self]
    exact BitVec.setWidth_eq _
  · exact RegUpd.gpr_write_of_ne _ _ _ (fun e => hq (by simp [e]))

theorem mul2_ok (s : State) {d₁ d₂ x y : Reg} (h₁ : d₁ ≠ x) (h₂ : d₁ ≠ y) (h₃ : d₁ ≠ d₂) :
    WP isa (.block [.mul .x d₁ x y, .umulh d₂ x y]) s fun t =>
      VG.Proof.X448.Wide.pair (t.gpr d₁) (t.gpr d₂) = (s.gpr x).toNat * (s.gpr y).toNat ∧ t.mem = s.mem ∧
      Keeps [d₁, d₂] s t := by
  refine WP.of_runBlock ⟨_, by simp only [runBlock_cons, runStep_some, runBlock_nil, exec]; rfl, ?_⟩
  refine ⟨?_, rfl, fun q hq => ?_, rfl, rfl⟩
  · simp only [State.read, BitVec.setWidth_eq, RegUpd.gpr_write, h₃, Ne.symm h₁, Ne.symm h₂,
      ite_true, ite_false]
    exact VG.Proof.Curve448.AArch64.Fast.mulPair (s.gpr x) (s.gpr y)
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    rw [RegUpd.gpr_write_of_ne _ _ _ hq.2, RegUpd.gpr_write_of_ne _ _ _ hq.1]

theorem addPair_ok (s : State) (a : Acc) {lo hi : Reg} (add : Bool) (h₁ : a.lo ≠ a.hi)
    (h₂ : a.lo ≠ hi) :
    WP isa (.block (addPair a lo hi add)) s fun t =>
      VG.Proof.Curve448.AArch64.Fast.accVal t a = (if add then (VG.Proof.Curve448.AArch64.Fast.accVal s a + VG.Proof.X448.Wide.pair (s.gpr lo) (s.gpr hi)) % VG.Proof.Curve448.AArch64.Fast.M
        else (VG.Proof.Curve448.AArch64.Fast.accVal s a + (VG.Proof.Curve448.AArch64.Fast.M - VG.Proof.X448.Wide.pair (s.gpr lo) (s.gpr hi))) % VG.Proof.Curve448.AArch64.Fast.M) ∧ t.mem = s.mem ∧
      Keeps [a.lo, a.hi] s t := by
  cases add
  all_goals
    refine WP.of_runBlock ⟨_, by
      simp only [addPair, Bool.false_eq_true, ite_false, ite_true, runBlock_cons, runStep_some,
        runBlock_nil, exec]; rfl, ?_⟩
    refine ⟨?_, rfl, fun q hq => ?_, rfl, rfl⟩
  rotate_left
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp only [read_x, RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hq.1, hq.2, ite_false]
  rotate_left
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp only [read_x, RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hq.1, hq.2, ite_false]
  · have := VG.Proof.Curve448.AArch64.Fast.subPair_mod (s.gpr a.lo) (s.gpr a.hi) (s.gpr lo) (s.gpr hi)
    simp only [VG.Proof.Curve448.AArch64.Fast.accVal, read_x, RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry, h₁, Ne.symm h₁,
      Ne.symm h₂, ite_true, ite_false, BitVec.setWidth_eq, Bool.false_eq_true]
    dsimp only [addCarry, carryOut, Size.bits] at this ⊢
    exact this
  · have := VG.Proof.Curve448.AArch64.Fast.addPair_mod (s.gpr a.lo) (s.gpr a.hi) (s.gpr lo) (s.gpr hi)
    simp only [VG.Proof.Curve448.AArch64.Fast.accVal, read_x, RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry, h₁, Ne.symm h₁,
      Ne.symm h₂, ite_true, ite_false, BitVec.setWidth_eq]
    dsimp only [addCarry, carryOut, Size.bits] at this ⊢
    exact this

/-! ## Registers of well-formed steps -/

section
variable {R : Regs} {accs : List Acc}

theorem lo_mem {a : Acc} (h : a ∈ accs) : a.lo ∈ VG.Proof.Curve448.AArch64.Fast.writes R accs :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_flatMap.mpr ⟨a, h, List.mem_cons_self⟩)))

theorem hi_mem {a : Acc} (h : a ∈ accs) : a.hi ∈ VG.Proof.Curve448.AArch64.Fast.writes R accs :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_flatMap.mpr ⟨a, h, List.mem_cons_of_mem _ List.mem_cons_self⟩)))

theorem t_mem : R.t ∈ VG.Proof.Curve448.AArch64.Fast.writes R accs := List.mem_cons_self
theorem p0_mem : R.p0 ∈ VG.Proof.Curve448.AArch64.Fast.writes R accs := List.mem_cons_of_mem _ List.mem_cons_self
theorem p1_mem : R.p1 ∈ VG.Proof.Curve448.AArch64.Fast.writes R accs :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

theorem accRegs_sub {r : Reg} (h : r ∈ VG.Proof.Curve448.AArch64.Fast.accRegs accs) : r ∈ VG.Proof.Curve448.AArch64.Fast.writes R accs :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))

theorem pair_sub {a : Acc} (h : a ∈ accs) {r : Reg} (hr : r ∈ [a.lo, a.hi]) : r ∈ VG.Proof.Curve448.AArch64.Fast.accRegs accs :=
  List.mem_flatMap.mpr ⟨a, h, hr⟩

theorem reg_not_mem {r : Reg} (h : VG.Proof.Curve448.AArch64.Fast.srcOk (VG.Proof.Curve448.AArch64.Fast.writes R accs) (.reg r) = true) :
    r ∉ VG.Proof.Curve448.AArch64.Fast.writes R accs := by
  intro hm
  simp [VG.Proof.Curve448.AArch64.Fast.srcOk, hm] at h

/-- A multiplicand's register is its temporary or is not written. -/
theorem reg?_cases {r : Reg} {x : Src} (h : VG.Proof.Curve448.AArch64.Fast.srcOk (VG.Proof.Curve448.AArch64.Fast.writes R accs) x = true) :
    x.reg? r = r ∨ x.reg? r ∉ VG.Proof.Curve448.AArch64.Fast.writes R accs := by
  cases x with
  | reg q => exact Or.inr (VG.Proof.Curve448.AArch64.Fast.reg_not_mem h)
  | mem d => exact Or.inl rfl
  | arg k => exact Or.inl rfl

theorem Good.acc (hG : VG.Proof.Curve448.AArch64.Fast.Good R accs) {a : Acc} (h : a ∈ accs) :
    a.lo ≠ a.hi ∧ a.lo ∉ [R.t, R.p0, R.p1] ∧ a.hi ∉ [R.t, R.p0, R.p1] := hG.2.2.2.1 a h

theorem Good.disj (hG : VG.Proof.Curve448.AArch64.Fast.Good R accs) {a c : Acc} (ha : a ∈ accs) (hc : c ∈ accs) (h : a ≠ c) :
    a.lo ∉ [c.lo, c.hi] ∧ a.hi ∉ [c.lo, c.hi] := hG.2.2.2.2.1 a ha c hc h

theorem Good.scr (hG : VG.Proof.Curve448.AArch64.Fast.Good R accs) {s t : State} {base : Addr} (hs : Scr s base) {rs : List Reg}
    (h : Keeps rs s t) (hrs : ∀ r ∈ rs, r ∈ VG.Proof.Curve448.AArch64.Fast.writes R accs) : Scr t base :=
  hs.of_keeps h ⟨fun e => hG.2.2.2.2.2.1 (hrs _ e), fun e => hG.2.2.2.2.2.2 (hrs _ e)⟩

end

/-! ## One step -/

def AccsEq (accs : List Acc) (s : State) (e : VG.Proof.Curve448.AArch64.Fast.Env) : Prop :=
  ∀ a ∈ accs, (VG.Proof.Curve448.AArch64.Fast.accVal s a : Int) = e a % VG.Proof.Curve448.AArch64.Fast.M

theorem accVal_keep {s t : State} {rs : List Reg} (h : Keeps rs s t) {a : Acc}
    (hlo : a.lo ∉ rs) (hhi : a.hi ∉ rs) : VG.Proof.Curve448.AArch64.Fast.accVal t a = VG.Proof.Curve448.AArch64.Fast.accVal s a := by
  simp only [VG.Proof.Curve448.AArch64.Fast.accVal, h.1 _ hlo, h.1 _ hhi]

theorem add_emod' {x p : Nat} {e f : Int} (h : (x : Int) = e % VG.Proof.Curve448.AArch64.Fast.M) (hp : (p : Int) = f % VG.Proof.Curve448.AArch64.Fast.M) :
    (((x + p) % VG.Proof.Curve448.AArch64.Fast.M : Nat) : Int) = (e + f) % VG.Proof.Curve448.AArch64.Fast.M := by
  rw [Int.natCast_emod, Int.natCast_add, h, hp, Int.emod_add_emod, Int.add_emod_emod]

theorem sub_emod' {x p : Nat} {e f : Int} (h : (x : Int) = e % VG.Proof.Curve448.AArch64.Fast.M) (hp : (p : Int) = f % VG.Proof.Curve448.AArch64.Fast.M)
    (hpM : p ≤ VG.Proof.Curve448.AArch64.Fast.M) : (((x + (VG.Proof.Curve448.AArch64.Fast.M - p)) % VG.Proof.Curve448.AArch64.Fast.M : Nat) : Int) = (e - f) % VG.Proof.Curve448.AArch64.Fast.M := by
  rw [Int.natCast_emod, Int.natCast_add, Int.natCast_sub hpM, h, hp, Int.emod_add_emod]
  rw [show e + ((VG.Proof.Curve448.AArch64.Fast.M : Nat) - f % (VG.Proof.Curve448.AArch64.Fast.M : Nat)) = (e - f % (VG.Proof.Curve448.AArch64.Fast.M : Nat)) + (VG.Proof.Curve448.AArch64.Fast.M : Nat) by omega,
    Int.add_emod_right, Int.sub_emod, Int.emod_emod_of_dvd _ (Int.dvd_refl _), ← Int.sub_emod]

theorem self_emod {x : Nat} (h : x < VG.Proof.Curve448.AArch64.Fast.M) : (x : Int) = (x : Int) % VG.Proof.Curve448.AArch64.Fast.M := by
  rw [← Int.natCast_emod, Nat.mod_eq_of_lt h]

theorem upd_self (e : VG.Proof.Curve448.AArch64.Fast.Env) (a : Acc) (v : Int) : VG.Proof.Curve448.AArch64.Fast.upd e a v a = v := by simp [VG.Proof.Curve448.AArch64.Fast.upd]
theorem upd_ne (e : VG.Proof.Curve448.AArch64.Fast.Env) {a c : Acc} (v : Int) (h : c ≠ a) : VG.Proof.Curve448.AArch64.Fast.upd e a v c = e c := by simp [VG.Proof.Curve448.AArch64.Fast.upd, h]

section
variable {R : Regs} {accs : List Acc} {base : Addr} {b : Nat}

theorem load_ok (hb8 : b % 8 = 0) (hb : b + 64 ≤ 8192) {s : State} (hs : Scr s base) (r : Reg)
    {x : Src} (hx : VG.Proof.Curve448.AArch64.Fast.srcOk (VG.Proof.Curve448.AArch64.Fast.writes R accs) x = true) :
    WP isa (.block (x.load b r)) s fun t =>
      (t.gpr (x.reg? r)).toNat = VG.Proof.Curve448.AArch64.Fast.srcVal s base b x ∧ t.mem = s.mem ∧ Keeps [r] s t := by
  cases x with
  | reg q => exact WP.block_nil ⟨rfl, rfl, Keeps.refl _ _⟩
  | mem d =>
    simp only [VG.Proof.Curve448.AArch64.Fast.srcOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hx
    exact WP.mono (VG.Proof.Curve448.AArch64.Fast.ld_ok hs r hx.1 hx.2) fun t ⟨h1, h2, h3⟩ =>
      ⟨by simp only [Src.reg?, h1, VG.Proof.Curve448.AArch64.Fast.srcVal], h2, h3⟩
  | arg k =>
    simp only [VG.Proof.Curve448.AArch64.Fast.srcOk, decide_eq_true_eq] at hx
    exact WP.mono (VG.Proof.Curve448.AArch64.Fast.ld_ok hs r (d := b + 8 * k) (by omega) (by omega))
      fun t ⟨h1, h2, h3⟩ => ⟨by simp only [Src.reg?, h1, VG.Proof.Curve448.AArch64.Fast.srcVal], h2, h3⟩

theorem loads_ok (hG : VG.Proof.Curve448.AArch64.Fast.Good R accs) (hb8 : b % 8 = 0) (hb : b + 64 ≤ 8192) {s : State}
    (hs : Scr s base) {x y : Src} (hx : VG.Proof.Curve448.AArch64.Fast.srcOk (VG.Proof.Curve448.AArch64.Fast.writes R accs) x = true)
    (hy : VG.Proof.Curve448.AArch64.Fast.srcOk (VG.Proof.Curve448.AArch64.Fast.writes R accs) y = true) :
    WP isa (.block (x.load b R.p0 ++ y.load b R.p1)) s fun t =>
      (t.gpr (x.reg? R.p0)).toNat = VG.Proof.Curve448.AArch64.Fast.srcVal s base b x ∧
      (t.gpr (y.reg? R.p1)).toNat = VG.Proof.Curve448.AArch64.Fast.srcVal s base b y ∧ t.mem = s.mem ∧
      Keeps [R.p0, R.p1] s t := by
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Curve448.AArch64.Fast.load_ok hb8 hb hs R.p0 hx) fun t ⟨tx, tm, tk⟩ => ?_
  have ts : Scr t base := hG.scr hs tk (by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; exact hr ▸ VG.Proof.Curve448.AArch64.Fast.p0_mem)
  refine WP.mono (VG.Proof.Curve448.AArch64.Fast.load_ok hb8 hb ts R.p1 hy) fun u ⟨uy, um, uk⟩ => ?_
  have xne : x.reg? R.p0 ∉ [R.p1] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rcases VG.Proof.Curve448.AArch64.Fast.reg?_cases (r := R.p0) hx with h | h
    · rw [h]; exact hG.2.2.1
    · exact fun e => h (e ▸ VG.Proof.Curve448.AArch64.Fast.p1_mem)
  have yv : VG.Proof.Curve448.AArch64.Fast.srcVal t base b y = VG.Proof.Curve448.AArch64.Fast.srcVal s base b y := by
    cases y with
    | reg q =>
      have hq := VG.Proof.Curve448.AArch64.Fast.reg_not_mem hy
      have hq' : q ∉ [R.p0] := fun e => hq (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at e
        exact e ▸ VG.Proof.Curve448.AArch64.Fast.p0_mem)
      simp only [VG.Proof.Curve448.AArch64.Fast.srcVal]
      rw [tk.1 q hq']
    | mem d => simp only [VG.Proof.Curve448.AArch64.Fast.srcVal, tm]
    | arg k => simp only [VG.Proof.Curve448.AArch64.Fast.srcVal, tm]
  refine ⟨by rw [uk.1 _ xne, tx], by rw [uy, yv], um.trans tm, ?_⟩
  refine (tk.mono ?_).trans (uk.mono ?_) <;> intro r hr <;> simp_all

theorem targets_ok (hG : VG.Proof.Curve448.AArch64.Fast.Good R accs) (P : Nat) (ts : List (Acc × Bool)) (hts : ∀ t ∈ ts, t.1 ∈ accs)
    {s : State} (hP : VG.Proof.X448.Wide.pair (s.gpr R.t) (s.gpr R.p1) = P) {e : VG.Proof.Curve448.AArch64.Fast.Env} (he : VG.Proof.Curve448.AArch64.Fast.AccsEq accs s e) :
    WP isa (.block (ts.flatMap fun a => addPair a.1 R.t R.p1 a.2)) s fun u =>
      VG.Proof.Curve448.AArch64.Fast.AccsEq accs u (ts.foldl (VG.Proof.Curve448.AArch64.Fast.target P) e) ∧ u.mem = s.mem ∧ Keeps (VG.Proof.Curve448.AArch64.Fast.accRegs accs) s u := by
  induction ts generalizing s e with
  | nil => exact WP.block_nil ⟨he, rfl, Keeps.refl _ _⟩
  | cons t ts ih =>
    have ht := hts t List.mem_cons_self
    obtain ⟨hlh, hlo, hhi⟩ := hG.acc ht
    rw [List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (VG.Proof.Curve448.AArch64.Fast.addPair_ok s t.1 t.2 hlh (fun e => hlo (by simp [e])))
      fun u ⟨uv, um, uk⟩ => ?_
    have tk : R.t ∉ [t.1.lo, t.1.hi] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨fun e => hlo (by simp [e]), fun e => hhi (by simp [e])⟩
    have pk : R.p1 ∉ [t.1.lo, t.1.hi] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨fun e => hlo (by simp [e]), fun e => hhi (by simp [e])⟩
    have hP' : VG.Proof.X448.Wide.pair (u.gpr R.t) (u.gpr R.p1) = P := by rw [uk.1 _ tk, uk.1 _ pk, hP]
    have he' : VG.Proof.Curve448.AArch64.Fast.AccsEq accs u (VG.Proof.Curve448.AArch64.Fast.target P e t) := by
      intro c hc
      by_cases hct : c = t.1
      · subst hct
        simp only [VG.Proof.Curve448.AArch64.Fast.target, VG.Proof.Curve448.AArch64.Fast.upd_self]
        rw [uv, ← hP]
        cases t.2
        · exact VG.Proof.Curve448.AArch64.Fast.sub_emod' (he _ hc) (VG.Proof.Curve448.AArch64.Fast.self_emod (VG.Proof.Curve448.AArch64.Fast.pair_lt _ _)) (Nat.le_of_lt (VG.Proof.Curve448.AArch64.Fast.pair_lt _ _))
        · exact VG.Proof.Curve448.AArch64.Fast.add_emod' (he _ hc) (VG.Proof.Curve448.AArch64.Fast.self_emod (VG.Proof.Curve448.AArch64.Fast.pair_lt _ _))
      · obtain ⟨d1, d2⟩ := hG.disj hc ht hct
        rw [VG.Proof.Curve448.AArch64.Fast.accVal_keep uk d1 d2, VG.Proof.Curve448.AArch64.Fast.target, VG.Proof.Curve448.AArch64.Fast.upd_ne _ _ hct]
        exact he c hc
    refine WP.mono (ih (fun t' h => hts t' (List.mem_cons_of_mem _ h)) hP' he')
      fun w ⟨wv, wm, wk⟩ => ⟨wv, wm.trans um, (uk.mono ?_).trans wk⟩
    intro r hr; exact VG.Proof.Curve448.AArch64.Fast.pair_sub ht hr

/-- Registers that are neither temporaries nor in an accumulator other than the written ones. -/
theorem other_acc (hG : VG.Proof.Curve448.AArch64.Fast.Good R accs) {a c : Acc} (ha : a ∈ accs) (hc : c ∈ accs) (h : c ≠ a)
    {rs : List Reg} (hrs : ∀ r ∈ rs, r ∈ [R.t, R.p0, R.p1] ∨ r ∈ [a.lo, a.hi]) :
    c.lo ∉ rs ∧ c.hi ∉ rs := by
  obtain ⟨-, hlo, hhi⟩ := hG.acc hc
  obtain ⟨d1, d2⟩ := hG.disj hc ha h
  exact ⟨fun e => (hrs _ e).elim hlo d1, fun e => (hrs _ e).elim hhi d2⟩

theorem mop_ok (hG : VG.Proof.Curve448.AArch64.Fast.Good R accs) (hb8 : b % 8 = 0) (hb : b + 64 ≤ 8192) {s : State}
    (hs : Scr s base) (op : MOp) (hop : VG.Proof.Curve448.AArch64.Fast.opOk (VG.Proof.Curve448.AArch64.Fast.writes R accs) accs op = true) {v : Src → Nat}
    (hv : ∀ x, VG.Proof.Curve448.AArch64.Fast.srcOk (VG.Proof.Curve448.AArch64.Fast.writes R accs) x = true → VG.Proof.Curve448.AArch64.Fast.srcVal s base b x = v x)
    {e : VG.Proof.Curve448.AArch64.Fast.Env} (he : VG.Proof.Curve448.AArch64.Fast.AccsEq accs s e) :
    WP isa (.block (op.code R b)) s fun t =>
      VG.Proof.Curve448.AArch64.Fast.AccsEq accs t (VG.Proof.Curve448.AArch64.Fast.opSem v e op) ∧ t.mem = s.mem ∧ Keeps (VG.Proof.Curve448.AArch64.Fast.writes R accs) s t := by
  have sub : ∀ r ∈ VG.Proof.Curve448.AArch64.Fast.accRegs accs, r ∈ VG.Proof.Curve448.AArch64.Fast.writes R accs := fun r h => VG.Proof.Curve448.AArch64.Fast.accRegs_sub h
  cases op with
  | set a x y =>
    simp only [VG.Proof.Curve448.AArch64.Fast.opOk, Bool.and_eq_true, List.contains_iff_mem] at hop
    obtain ⟨⟨ha, hx⟩, hy⟩ := hop
    obtain ⟨hlh, hlo, hhi⟩ := hG.acc ha
    simp only [MOp.code, List.append_assoc]
    rw [← List.append_assoc, WP.block_append_iff]
    refine WP.mono (VG.Proof.Curve448.AArch64.Fast.loads_ok hG hb8 hb hs hx hy) fun t ⟨tx, ty, tm, tk⟩ => ?_
    have nx : a.lo ≠ x.reg? R.p0 := by
      rcases VG.Proof.Curve448.AArch64.Fast.reg?_cases (r := R.p0) hx with h | h
      · rw [h]; exact fun e => hlo (by simp [e])
      · exact fun e => h (e ▸ VG.Proof.Curve448.AArch64.Fast.lo_mem ha)
    have ny : a.lo ≠ y.reg? R.p1 := by
      rcases VG.Proof.Curve448.AArch64.Fast.reg?_cases (r := R.p1) hy with h | h
      · rw [h]; exact fun e => hlo (by simp [e])
      · exact fun e => h (e ▸ VG.Proof.Curve448.AArch64.Fast.lo_mem ha)
    refine WP.mono (VG.Proof.Curve448.AArch64.Fast.mul2_ok t nx ny hlh) fun u ⟨uv, um, uk⟩ => ⟨?_, um.trans tm, ?_⟩
    · intro c hc
      by_cases hca : c = a
      · subst hca
        simp only [VG.Proof.Curve448.AArch64.Fast.opSem, VG.Proof.Curve448.AArch64.Fast.upd_self]
        change ((VG.Proof.X448.Wide.pair (u.gpr c.lo) (u.gpr c.hi) : Nat) : Int) = _
        have hlt : v x * v y < VG.Proof.Curve448.AArch64.Fast.M := by
          rw [← hv x hx, ← hv y hy, ← tx, ← ty, ← uv]; exact VG.Proof.Curve448.AArch64.Fast.pair_lt _ _
        rw [uv, tx, ty, hv x hx, hv y hy, ← Int.natCast_mul]
        exact VG.Proof.Curve448.AArch64.Fast.self_emod hlt
      · obtain ⟨n1, n2⟩ := VG.Proof.Curve448.AArch64.Fast.other_acc hG ha hc hca (rs := [R.p0, R.p1]) (by simp)
        obtain ⟨n3, n4⟩ := VG.Proof.Curve448.AArch64.Fast.other_acc hG ha hc hca (rs := [a.lo, a.hi]) (by simp)
        rw [VG.Proof.Curve448.AArch64.Fast.accVal_keep uk n3 n4, VG.Proof.Curve448.AArch64.Fast.accVal_keep tk n1 n2]
        simp only [VG.Proof.Curve448.AArch64.Fast.opSem, VG.Proof.Curve448.AArch64.Fast.upd_ne _ _ hca]
        exact he c hc
    · refine (tk.mono ?_).trans (uk.mono ?_)
      · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact VG.Proof.Curve448.AArch64.Fast.p0_mem
        · exact VG.Proof.Curve448.AArch64.Fast.p1_mem
      · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact VG.Proof.Curve448.AArch64.Fast.lo_mem ha
        · exact VG.Proof.Curve448.AArch64.Fast.hi_mem ha
  | prod x y ts =>
    simp only [VG.Proof.Curve448.AArch64.Fast.opOk, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at hop
    obtain ⟨⟨hx, hy⟩, hts⟩ := hop
    simp only [MOp.code, List.append_assoc]
    rw [← List.append_assoc, WP.block_append_iff]
    refine WP.mono (VG.Proof.Curve448.AArch64.Fast.loads_ok hG hb8 hb hs hx hy) fun t ⟨tx, ty, tm, tk⟩ => ?_
    have ts' : Scr t base := hG.scr hs tk (by simp [VG.Proof.Curve448.AArch64.Fast.p0_mem, VG.Proof.Curve448.AArch64.Fast.p1_mem])
    have nx : R.t ≠ x.reg? R.p0 := by
      rcases VG.Proof.Curve448.AArch64.Fast.reg?_cases (r := R.p0) hx with h | h
      · rw [h]; exact hG.1
      · exact fun e => h (e ▸ VG.Proof.Curve448.AArch64.Fast.t_mem)
    have ny : R.t ≠ y.reg? R.p1 := by
      rcases VG.Proof.Curve448.AArch64.Fast.reg?_cases (r := R.p1) hy with h | h
      · rw [h]; exact hG.2.1
      · exact fun e => h (e ▸ VG.Proof.Curve448.AArch64.Fast.t_mem)
    rw [WP.block_append_iff]
    refine WP.mono (VG.Proof.Curve448.AArch64.Fast.mul2_ok t nx ny hG.2.1) fun u ⟨uv, um, uk⟩ => ?_
    have he' : VG.Proof.Curve448.AArch64.Fast.AccsEq accs u e := by
      intro c hc
      obtain ⟨-, hlo, hhi⟩ := hG.acc hc
      have n1 : c.lo ∉ [R.p0, R.p1] := fun h => hlo (by simp at h; rcases h with h | h <;> simp [h])
      have n2 : c.hi ∉ [R.p0, R.p1] := fun h => hhi (by simp at h; rcases h with h | h <;> simp [h])
      have n3 : c.lo ∉ [R.t, R.p1] := fun h => hlo (by simp at h; rcases h with h | h <;> simp [h])
      have n4 : c.hi ∉ [R.t, R.p1] := fun h => hhi (by simp at h; rcases h with h | h <;> simp [h])
      rw [VG.Proof.Curve448.AArch64.Fast.accVal_keep uk n3 n4, VG.Proof.Curve448.AArch64.Fast.accVal_keep tk n1 n2]
      exact he c hc
    have hP : VG.Proof.X448.Wide.pair (u.gpr R.t) (u.gpr R.p1) = v x * v y := by rw [uv, tx, ty, hv x hx, hv y hy]
    refine WP.mono (VG.Proof.Curve448.AArch64.Fast.targets_ok hG _ ts hts hP he') fun w ⟨wv, wm, wk⟩ =>
      ⟨by simpa only [VG.Proof.Curve448.AArch64.Fast.opSem, Int.natCast_mul] using wv, wm.trans (um.trans tm), ?_⟩
    refine ((tk.mono ?_).trans (uk.mono ?_)).trans (wk.mono sub)
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact VG.Proof.Curve448.AArch64.Fast.p0_mem
      · exact VG.Proof.Curve448.AArch64.Fast.p1_mem
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact VG.Proof.Curve448.AArch64.Fast.t_mem
      · exact VG.Proof.Curve448.AArch64.Fast.p1_mem
  | merge d c add =>
    simp only [VG.Proof.Curve448.AArch64.Fast.opOk, Bool.and_eq_true, List.contains_iff_mem, bne_iff_ne, ne_eq] at hop
    obtain ⟨⟨hd, hc⟩, hdc⟩ := hop
    obtain ⟨hlh, -, -⟩ := hG.acc hd
    obtain ⟨d1, -⟩ := hG.disj hd hc hdc
    have nh : d.lo ≠ c.hi := fun e => d1 (by simp [e])
    simp only [MOp.code]
    refine WP.mono (VG.Proof.Curve448.AArch64.Fast.addPair_ok s d add hlh nh) fun u ⟨uv, um, uk⟩ => ⟨?_, um, uk.mono ?_⟩
    · intro a ha
      by_cases had : a = d
      · subst had
        simp only [VG.Proof.Curve448.AArch64.Fast.opSem, VG.Proof.Curve448.AArch64.Fast.upd_self]
        change ((VG.Proof.Curve448.AArch64.Fast.accVal u a : Nat) : Int) = _
        rw [uv]
        have hcv : ((VG.Proof.X448.Wide.pair (s.gpr c.lo) (s.gpr c.hi) : Nat) : Int) = e c % VG.Proof.Curve448.AArch64.Fast.M := he c hc
        cases add
        · exact VG.Proof.Curve448.AArch64.Fast.sub_emod' (he a ha) hcv (Nat.le_of_lt (VG.Proof.Curve448.AArch64.Fast.pair_lt _ _))
        · exact VG.Proof.Curve448.AArch64.Fast.add_emod' (he a ha) hcv
      · obtain ⟨n1, n2⟩ := hG.disj ha hd had
        rw [VG.Proof.Curve448.AArch64.Fast.accVal_keep uk n1 n2]
        simp only [VG.Proof.Curve448.AArch64.Fast.opSem, VG.Proof.Curve448.AArch64.Fast.upd_ne _ _ had]
        exact he a ha
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact VG.Proof.Curve448.AArch64.Fast.lo_mem hd
      · exact VG.Proof.Curve448.AArch64.Fast.hi_mem hd

theorem mops_ok (hG : VG.Proof.Curve448.AArch64.Fast.Good R accs) (hb8 : b % 8 = 0) (hb : b + 64 ≤ 8192) (ops : List MOp)
    (hops : ops.all (VG.Proof.Curve448.AArch64.Fast.opOk (VG.Proof.Curve448.AArch64.Fast.writes R accs) accs) = true) {s : State} (hs : Scr s base)
    {v : Src → Nat} (hv : ∀ x, VG.Proof.Curve448.AArch64.Fast.srcOk (VG.Proof.Curve448.AArch64.Fast.writes R accs) x = true → VG.Proof.Curve448.AArch64.Fast.srcVal s base b x = v x)
    {e : VG.Proof.Curve448.AArch64.Fast.Env} (he : VG.Proof.Curve448.AArch64.Fast.AccsEq accs s e) :
    WP isa (.block (ops.flatMap (MOp.code R b))) s fun t =>
      VG.Proof.Curve448.AArch64.Fast.AccsEq accs t (VG.Proof.Curve448.AArch64.Fast.sem v e ops) ∧ t.mem = s.mem ∧ Keeps (VG.Proof.Curve448.AArch64.Fast.writes R accs) s t := by
  induction ops generalizing s e with
  | nil => exact WP.block_nil ⟨he, rfl, Keeps.refl _ _⟩
  | cons op ops ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hops
    rw [List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (VG.Proof.Curve448.AArch64.Fast.mop_ok hG hb8 hb hs op hops.1 hv he) fun t ⟨tv, tm, tk⟩ => ?_
    have hv' : ∀ x, VG.Proof.Curve448.AArch64.Fast.srcOk (VG.Proof.Curve448.AArch64.Fast.writes R accs) x = true → VG.Proof.Curve448.AArch64.Fast.srcVal t base b x = v x := by
      intro x hx
      rw [← hv x hx]
      cases x with
      | reg q => simp only [VG.Proof.Curve448.AArch64.Fast.srcVal, tk.1 q (VG.Proof.Curve448.AArch64.Fast.reg_not_mem hx)]
      | mem d => simp only [VG.Proof.Curve448.AArch64.Fast.srcVal, tm]
      | arg k => simp only [VG.Proof.Curve448.AArch64.Fast.srcVal, tm]
    refine WP.mono (ih hops.2 (hG.scr hs tk (fun _ h => h)) hv' tv) fun u ⟨uv, um, uk⟩ =>
      ⟨uv, um.trans tm, tk.trans uk⟩

end

end VG.Proof.Curve448.AArch64.Fast

end

/- Proofs formerly in `VerifiedGarbage.Proof.Curve448.AArch64.Fast.ColEnd`. -/
section

/-!
# The end of a column: carry in, stage a limb, carry out

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Curve448.AArch64.Fast

open VG VG.AArch64 VG.Proof.Ed25519.Word64
open VG.Impl.Curve448.AArch64.Fast
open VG.Impl.X448.AArch64 (ld st)
open VG.Proof.X448.Wide (pair low56 add128 radix)
open VG.Proof.X448.AArch64 (Keeps Scr word off load_sc addr_word read8_eq write8_eq)
open VG.Proof.Ed25519.AArch64 (read_x)

theorem extr56 (lo hi : BitVec 64) :
    ((hi ++ lo).extractLsb' 56 64).toNat = VG.Proof.X448.Wide.pair lo hi / 2 ^ 56 % 2 ^ 64 := by
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt lo.isLt,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  simp only [VG.Proof.X448.Wide.pair]
  congr 2
  omega

theorem mask_val : (BitVec.ofNat 64 (2 ^ 56 - 1) : BitVec 64) =
    (0x00ff : BitVec 16).setWidth 64 <<< 48 ||| ((0xffff : BitVec 16).setWidth 64 <<< 32 |||
      ((0xffff : BitVec 16).setWidth 64 <<< 16 ||| (0xffff : BitVec 16).setWidth 64)) := by
  decide

/-- Add the carry `c`: `ZERO` holds zero. -/
theorem carryIn_ok (s : State) (a : Acc) (c : Reg) (h₁ : a.lo ≠ a.hi) (h₂ : a.lo ≠ ZERO)
    (hz : s.gpr ZERO = 0) (hlt : VG.Proof.Curve448.AArch64.Fast.accVal s a + (s.gpr c).toNat < 2 ^ 128) :
    WP isa (.block [.adds .x a.lo a.lo c, .adc .x a.hi a.hi ZERO]) s fun t =>
      VG.Proof.Curve448.AArch64.Fast.accVal t a = VG.Proof.Curve448.AArch64.Fast.accVal s a + (s.gpr c).toNat ∧ t.mem = s.mem ∧ Keeps [a.lo, a.hi] s t := by
  refine WP.of_runBlock ⟨_, by simp only [runBlock_cons, runStep_some, runBlock_nil, exec]; rfl, ?_⟩
  refine ⟨?_, rfl, fun q hq => ?_, rfl, rfl⟩
  · have := add128 (s.gpr a.lo) (s.gpr a.hi) (s.gpr c) hlt
    simp only [VG.Proof.Curve448.AArch64.Fast.accVal, read_x, RegUpd.gpr_write, RegUpd.gpr_addWithCarry,
      RegUpd.c_addWithCarry, h₁, Ne.symm h₁, Ne.symm h₂, ite_true, ite_false, BitVec.setWidth_eq, hz]
    dsimp only [addCarry, carryOut, Size.bits] at this ⊢
    exact this
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp only [read_x, RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hq.1, hq.2, ite_false]

/-- Store the low 56 bits of `a` at `d` and carry the rest into `c`. -/
theorem stage_ok {s : State} {base : Addr} (hs : Scr s base) (t : Reg) (a : Acc) (c : Reg)
    {d : Nat} (hd8 : d % 8 = 0) (hd : d + 8 ≤ 8192) (h₁ : t ≠ a.lo) (h₂ : t ≠ a.hi) (h₄ : t ≠ .x3)
    (hm : s.gpr MASK = BitVec.ofNat 64 (2 ^ 56 - 1)) (hlt : VG.Proof.Curve448.AArch64.Fast.accVal s a < 2 ^ 120) :
    WP isa (.block [.logic .and .x t a.lo MASK, st t d, .extr .x c a.hi a.lo 56]) s
      fun u => u.mem = s.mem.writeW (off base d) (BitVec.ofNat 64 (VG.Proof.Curve448.AArch64.Fast.accVal s a % VG.Proof.X448.Wide.radix)) ∧
        (u.gpr c).toNat = VG.Proof.Curve448.AArch64.Fast.accVal s a / VG.Proof.X448.Wide.radix ∧ Keeps [t, c] s u := by
  have w := hs.write (d := d) (n := 8) hd
  have oe : d % 8 = 0 ∧ d < 32768 := ⟨hd8, by omega⟩
  have hv : (s.gpr a.lo &&& s.gpr MASK) = BitVec.ofNat 64 (VG.Proof.Curve448.AArch64.Fast.accVal s a % VG.Proof.X448.Wide.radix) := by
    apply BitVec.eq_of_toNat_eq
    rw [hm, low56 (s.gpr a.lo) (s.gpr a.hi), BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide))]
    rfl
  refine WP.of_runBlock ⟨_, by
    simp only [st, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes, Size.bits,
      read_x, State.store, RegUpd.gpr_write, RegUpd.wr_write, oe, and_self, Ne.symm h₄,
      ite_false, hs.x3, w, ite_true, Option.bind_some, show 56 < 64 from by decide]; rfl, ?_⟩
  refine ⟨?_, ?_, fun q hq => ?_, rfl, rfl⟩
  · simp only [RegUpd.mem_write, BitVec.setWidth_eq, write8_eq, hv]
  · simp only [RegUpd.gpr_write, ite_true, Ne.symm h₁, Ne.symm h₂, ite_false]
    rw [BitVec.setWidth_eq, VG.Proof.Curve448.AArch64.Fast.extr56, Nat.mod_eq_of_lt (by
      have := hlt; unfold VG.Proof.Curve448.AArch64.Fast.accVal at this; omega)]
    rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp only [RegUpd.gpr_write, hq.1, hq.2, ite_false]

end VG.Proof.Curve448.AArch64.Fast

end

/- Proofs formerly in `VerifiedGarbage.Proof.Curve448.AArch64.Fast.Finish`. -/
section

/-!
# The end of a product: the last carries and the result

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Curve448.AArch64.Fast

open VG VG.AArch64
open VG.Impl.Curve448.AArch64.Fast
open VG.Impl.X448.AArch64 (ld st)
open VG.Proof.X448.Wide (radix)
open VG.Proof.X448.AArch64 (Keeps Scr word off Outside writeW_outside write8_eq read8_eq limbs)
open VG.Proof.Ed25519.AArch64 (read_x)

theorem read8_eq_word (m : Mem) (base : Addr) (d : Nat) :
    m.read (base + BitVec.ofNat 64 d) 8 = word m base d := by
  simp only [word, off, Mem.readW, BitVec.setWidth_eq]

theorem word_writeW (m : Mem) (base : Addr) {d d' : Nat} (hd : d + 8 ≤ 8192) (hd' : d' + 8 ≤ 8192)
    (h : d' = d ∨ d' + 8 ≤ d ∨ d + 8 ≤ d') (v : BitVec 64) :
    word (m.writeW (off base d) v) base d' = if d' = d then v else word m base d' := by
  by_cases e : d' = d
  · rw [ite_eq_left e, e, word, Mem.readW_writeW_self64]
  · rw [ite_eq_right e]
    exact Mem.readW_writeW_sep (Offset.sep base (by omega) (by omega) (by omega)) (by decide)

theorem readW_writeW' (m : Mem) (base : Addr) {d d' : Nat} (hd : d + 8 ≤ 8192)
    (hd' : d' + 8 ≤ 8192) (h : d' = d ∨ d' + 8 ≤ d ∨ d + 8 ≤ d') (v : BitVec 64) :
    (m.writeW (base + BitVec.ofNat 64 d) v).readW (base + BitVec.ofNat 64 d') 64 =
      if d' = d then v else m.readW (base + BitVec.ofNat 64 d') 64 :=
  VG.Proof.Curve448.AArch64.Fast.word_writeW m base hd hd' h v

theorem st_ok {s : State} {base : Addr} (hs : Scr s base) (r : Reg) {d : Nat}
    (h8 : d % 8 = 0) (hd : d + 8 ≤ 8192) :
    WP isa (.block [st r d]) s fun t =>
      t.mem = s.mem.writeW (off base d) (s.gpr r) ∧ Keeps [] s t := by
  have w := hs.write (d := d) (n := 8) hd
  have oe : d % 8 = 0 ∧ d < 32768 := ⟨h8, by omega⟩
  refine WP.of_runBlock ⟨_, by
    simp only [st, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes, read_x,
      State.store, oe, and_self, hs.x3, w, ite_true, Option.bind_some]; rfl, ?_⟩
  exact ⟨by simp only [BitVec.setWidth_eq, write8_eq], fun _ _ => rfl, rfl, rfl⟩

def finA : List Instr :=
  [.add .x .x4 .x4 CH, .add .x .x6 .x6 CH, .add .x .x6 .x6 CL,
    .lsr .x .x8 .x4 56, .logic .and .x .x4 .x4 MASK, .add .x .x5 .x5 .x8,
    .lsr .x .x8 .x6 56, .logic .and .x .x6 .x6 MASK, .add .x .x7 .x7 .x8]

theorem finA_ok (s : State) (hm : s.gpr MASK = BitVec.ofNat 64 (2 ^ 56 - 1))
    {l0 l1 l4 l5 cl ch : Nat} (h0 : (s.gpr .x4).toNat = l0) (h1 : (s.gpr .x5).toNat = l1)
    (h4 : (s.gpr .x6).toNat = l4) (h5 : (s.gpr .x7).toNat = l5)
    (hl : (s.gpr CL).toNat = cl) (hh : (s.gpr CH).toNat = ch)
    (c0 : l0 + ch < 2 ^ 64) (c4 : l4 + cl + ch < 2 ^ 64) (b1 : l1 < 2 ^ 56) (b5 : l5 < 2 ^ 56) :
    WP isa (.block VG.Proof.Curve448.AArch64.Fast.finA) s fun t =>
      (t.gpr .x4).toNat = (l0 + ch) % VG.Proof.X448.Wide.radix ∧ (t.gpr .x5).toNat = l1 + (l0 + ch) / VG.Proof.X448.Wide.radix ∧
      (t.gpr .x6).toNat = (l4 + cl + ch) % VG.Proof.X448.Wide.radix ∧ (t.gpr .x7).toNat = l5 + (l4 + cl + ch) / VG.Proof.X448.Wide.radix ∧
      t.mem = s.mem ∧ Keeps [.x4, .x5, .x6, .x7, .x8] s t := by
  refine WP.of_runBlock ⟨_, by
    simp only [VG.Proof.Curve448.AArch64.Fast.finA, runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
      show 56 < 64 from by decide, ite_true]; rfl, ?_⟩
  have m56 : ∀ x : BitVec 64, (x &&& BitVec.ofNat 64 (2 ^ 56 - 1)).toNat = x.toNat % VG.Proof.X448.Wide.radix := by
    intro x
    rw [BitVec.toNat_and, show (BitVec.ofNat 64 (2 ^ 56 - 1)).toNat = 2 ^ 56 - 1 by decide,
      Nat.and_two_pow_sub_one_eq_mod]
    rfl
  simp only [CL, CH, MASK] at hm hl hh
  simp only [State.read, RegUpd.gpr_write, BitVec.setWidth_eq, CL, CH, MASK,
    reduceCtorEq, ite_true, ite_false, hm]
  refine ⟨?_, ?_, ?_, ?_, rfl, fun q hq => ?_, rfl, rfl⟩
  · rw [m56, BitVec.toNat_add, h0, hh, Nat.mod_eq_of_lt c0]
  · rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_add, h1, h0, hh,
      Nat.mod_eq_of_lt c0, Nat.shiftRight_eq_div_pow]
    simp only [VG.Proof.X448.Wide.radix]
    omega
  · rw [m56, BitVec.toNat_add, BitVec.toNat_add, h4, hh, hl,
      Nat.mod_eq_of_lt (by omega : l4 + ch < 2 ^ 64), Nat.mod_eq_of_lt (by omega : l4 + ch + cl < 2 ^ 64)]
    congr 1; omega
  · rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_add, h5, h4,
      hh, hl, Nat.mod_eq_of_lt (by omega : l4 + ch < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : l4 + ch + cl < 2 ^ 64), Nat.shiftRight_eq_div_pow]
    simp only [VG.Proof.X448.Wide.radix]
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp only [RegUpd.gpr_write, hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1, hq.2.2.2.2, ite_false]

/-- The limbs that `finish` writes. -/
def finVal (l : Nat → Nat) (cl ch : Nat) (i : Nat) : Nat :=
  match i with
  | 0 => (l 0 + ch) % VG.Proof.X448.Wide.radix
  | 1 => l 1 + (l 0 + ch) / VG.Proof.X448.Wide.radix
  | 4 => (l 4 + cl + ch) % VG.Proof.X448.Wide.radix
  | 5 => l 5 + (l 4 + cl + ch) / VG.Proof.X448.Wide.radix
  | i => l i

theorem finish_split (o : Nat) : finish o =
    [ld .x4 o, ld .x5 (o + 8), ld .x6 (o + 32), ld .x7 (o + 40)] ++ VG.Proof.Curve448.AArch64.Fast.finA ++
    [st .x4 o, st .x5 (o + 8), st .x6 (o + 32), st .x7 (o + 40)] := rfl

theorem finish_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat} (ho : o + 64 ≤ 8192)
    (ho8 : o % 8 = 0) (hm : s.gpr MASK = BitVec.ofNat 64 (2 ^ 56 - 1)) {l : Nat → Nat}
    (hl : ∀ i < 8, (word s.mem base (o + 8 * i)).toNat = l i) (hb : ∀ i < 8, l i < VG.Proof.X448.Wide.radix)
    {cl ch : Nat} (hcl : (s.gpr CL).toNat = cl) (hch : (s.gpr CH).toNat = ch)
    (c0 : l 0 + ch < 2 ^ 64) (c4 : l 4 + cl + ch < 2 ^ 64) :
    WP isa (.block (finish o)) s fun t =>
      (∀ i < 8, limbs t.mem base o i = VG.Proof.Curve448.AArch64.Fast.finVal l cl ch i) ∧ Outside base o 64 s.mem t.mem ∧
      Keeps [.x4, .x5, .x6, .x7, .x8] s t := by
  have rd : ∀ d, d + 8 ≤ 8192 → InRegions (s.rd ++ s.wr) (off base d) 8 := fun d hd => hs.read hd
  have ae : ∀ d, d % 8 = 0 → d + 8 ≤ 8192 → d % 8 = 0 ∧ d < 32768 := fun d h1 h2 => ⟨h1, by omega⟩
  rw [VG.Proof.Curve448.AArch64.Fast.finish_split, List.append_assoc, WP.block_append_iff]
  refine WP.mono (WP.of_runBlock ⟨_, by
    simp only [ld, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes, State.load,
      RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
      reduceCtorEq, ite_false, hs.x3, ae o ho8 (by omega),
      ae (o + 8) (by omega) (by omega), ae (o + 32) (by omega) (by omega),
      ae (o + 40) (by omega) (by omega), and_self, ite_true,
      rd o (by omega), rd (o + 8) (by omega), rd (o + 32) (by omega),
      rd (o + 40) (by omega), Option.map_some, Option.bind_some]; rfl, rfl⟩) fun t ht => ?_
  subst ht
  rw [WP.block_append_iff]
  have wv : ∀ i < 8, (word s.mem base (o + 8 * i)).toNat = l i := hl
  refine WP.mono (VG.Proof.Curve448.AArch64.Fast.finA_ok _ (by simp only [RegUpd.gpr_write, MASK, reduceCtorEq, ite_false]; exact hm)
    (l0 := l 0) (l1 := l 1) (l4 := l 4) (l5 := l 5)
    (by simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq, VG.Proof.Curve448.AArch64.Fast.read8_eq_word]; exact wv 0 (by decide))
    (by simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq, VG.Proof.Curve448.AArch64.Fast.read8_eq_word]; exact wv 1 (by decide))
    (by simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq, VG.Proof.Curve448.AArch64.Fast.read8_eq_word]; exact wv 4 (by decide))
    (by simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq, VG.Proof.Curve448.AArch64.Fast.read8_eq_word]; exact wv 5 (by decide))
    (by simp only [RegUpd.gpr_write, CL, reduceCtorEq, ite_false]; exact hcl)
    (by simp only [RegUpd.gpr_write, CH, reduceCtorEq, ite_false]; exact hch)
    c0 c4 (hb 1 (by decide)) (hb 5 (by decide))) fun u ⟨u4, u5, u6, u7, um, uk⟩ => ?_
  have u3 : u.gpr .x3 = base := by
    rw [uk.1 .x3 (by decide)]
    simp only [RegUpd.gpr_write, reduceCtorEq, ite_false]
    exact hs.x3
  have u12 : u.gpr .x12 = 0x0fffffff := by
    rw [uk.1 .x12 (by decide)]
    simp only [RegUpd.gpr_write, reduceCtorEq, ite_false]
    exact hs.mask
  have us : Scr u base := ⟨u3, u12, uk.2.2 ▸ hs.wr, hs.nowrap⟩
  have mu : u.mem = s.mem := um
  -- the four stores
  have sw : ∀ (t : State) (r : Reg) (d : Nat), Scr t base → d % 8 = 0 → d + 8 ≤ 8192 →
      WP isa (.block [st r d]) t fun t' =>
        (∀ d', d' + 8 ≤ 8192 → (d' = d ∨ d' + 8 ≤ d ∨ d + 8 ≤ d') →
          word t'.mem base d' = if d' = d then t.gpr r else word t.mem base d') ∧
        Outside base d 8 t.mem t'.mem ∧ t'.gpr = t.gpr ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
    intro t r d ht h8 hd
    refine WP.mono (VG.Proof.Curve448.AArch64.Fast.st_ok ht r h8 hd) fun t' ⟨hm, hk⟩ => ⟨fun d' hd' hs => ?_, ?_, ?_, hk.2.1, hk.2.2⟩
    · rw [hm]; exact VG.Proof.Curve448.AArch64.Fast.word_writeW _ _ hd hd' hs _
    · rw [hm]; exact writeW_outside _ _ _ hd
    · funext q; exact hk.1 q (by simp)
  rw [show ([st .x4 o, st .x5 (o + 8), st .x6 (o + 32), st .x7 (o + 40)] : List Instr) =
      [st .x4 o] ++ [st .x5 (o + 8)] ++ [st .x6 (o + 32)] ++ [st .x7 (o + 40)] from rfl]
  simp only [List.append_assoc]
  have ss : ∀ t : State, t.gpr .x3 = base → t.gpr .x12 = 0x0fffffff → t.wr = u.wr → Scr t base :=
    fun t h1 h2 h3 => ⟨h1, h2, h3 ▸ us.wr, hs.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (sw u .x4 (o) us (by omega) (by omega)) fun t1 ⟨t1w, t1o, t1g, t1r, t1wr⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (sw t1 .x5 (o + 8) (ss t1 (by simp only [*]) (by simp only [*]) (by simp only [*])) (by omega) (by omega)) fun t2 ⟨t2w, t2o, t2g, t2r, t2wr⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (sw t2 .x6 (o + 32) (ss t2 (by simp only [*]) (by simp only [*]) (by simp only [*])) (by omega) (by omega)) fun t3 ⟨t3w, t3o, t3g, t3r, t3wr⟩ => ?_
  refine WP.mono (sw t3 .x7 (o + 40) (ss t3 (by simp only [*]) (by simp only [*]) (by simp only [*])) (by omega) (by omega)) fun t4 ⟨t4w, t4o, t4g, t4r, t4wr⟩ => ?_
  have keep : ∀ d, d + 8 ≤ 8192 → (d + 8 ≤ o ∨ o + 8 ≤ d) → (d + 8 ≤ o + 8 ∨ o + 16 ≤ d) →
      (d + 8 ≤ o + 32 ∨ o + 40 ≤ d) → (d + 8 ≤ o + 40 ∨ o + 48 ≤ d) →
      word t4.mem base d = word s.mem base d := by
    intro d hd h1 h2 h3 h4
    rw [t4w d hd (by omega), ite_eq_right (by omega), t3w d hd (by omega), ite_eq_right (by omega),
      t2w d hd (by omega), ite_eq_right (by omega), t1w d hd (by omega), ite_eq_right (by omega), mu]
  refine ⟨fun i hi => ?_, ?_, ?_⟩
  · obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
        i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
    · change (word t4.mem base (o)).toNat = _
      rw [t4w (o) (by omega) (by omega), ite_eq_right (by omega), t3w (o) (by omega) (by omega), ite_eq_right (by omega), t2w (o) (by omega) (by omega), ite_eq_right (by omega), t1w (o) (by omega) (by omega), ite_eq_left rfl]
      rw [u4]; rfl
    · change (word t4.mem base (o + 8)).toNat = _
      rw [t4w (o + 8) (by omega) (by omega), ite_eq_right (by omega), t3w (o + 8) (by omega) (by omega), ite_eq_right (by omega), t2w (o + 8) (by omega) (by omega), ite_eq_left rfl]
      rw [t1g]
      rw [u5]; rfl
    · change (word t4.mem base (o + 16)).toNat = _
      rw [keep _ (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact hl 2 (by decide)
    · change (word t4.mem base (o + 24)).toNat = _
      rw [keep _ (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact hl 3 (by decide)
    · change (word t4.mem base (o + 32)).toNat = _
      rw [t4w (o + 32) (by omega) (by omega), ite_eq_right (by omega), t3w (o + 32) (by omega) (by omega), ite_eq_left rfl]
      rw [t2g, t1g]
      rw [u6]; rfl
    · change (word t4.mem base (o + 40)).toNat = _
      rw [t4w (o + 40) (by omega) (by omega), ite_eq_left rfl]
      rw [t3g, t2g, t1g]
      rw [u7]; rfl
    · change (word t4.mem base (o + 48)).toNat = _
      rw [keep _ (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact hl 6 (by decide)
    · change (word t4.mem base (o + 56)).toNat = _
      rw [keep _ (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact hl 7 (by decide)
  · rw [← mu]
    have w : ∀ {m m' : Mem} {d : Nat}, Outside base d 8 m m' → o ≤ d → d + 8 ≤ o + 64 →
        Outside base o 64 m m' := fun h h1 h2 => h.mono h1 h2
    exact (w t1o (by omega) (by omega)).trans ((w t2o (by omega) (by omega)).trans
      ((w t3o (by omega) (by omega)).trans (w t4o (by omega) (by omega))))
  · refine ⟨fun q hq => ?_, ?_, ?_⟩
    · rw [t4g, t3g, t2g, t1g, uk.1 q hq]
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
      simp only [RegUpd.gpr_write, hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1, ite_false]
    · rw [t4r, t3r, t2r, t1r, uk.2.1]; rfl
    · rw [t4wr, t3wr, t2wr, t1wr, uk.2.2]; rfl

end VG.Proof.Curve448.AArch64.Fast

end

/- Proofs formerly in `VerifiedGarbage.Proof.Curve448.AArch64.Fast.Prelude`. -/
section

/-!
# The start of a product: operands in registers, constants, operand sums

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Curve448.AArch64.Fast

open VG VG.AArch64
open VG.Impl.Curve448.AArch64.Fast
open VG.Impl.X448.AArch64 (ld st ACC)
open VG.Proof.X448.AArch64 (Scr)
open VG.Proof.X448.Wide (radix)
open VG.Proof.X448.AArch64 (Keeps Scr word off Outside writeW_outside limbs)
open VG.Proof.Ed25519.AArch64 (read_x)

theorem A_inj : ∀ i < 8, ∀ j < 8, i ≠ j → Mul.A i ≠ Mul.A j := by decide

theorem A_mem : ∀ i < 8, Mul.A i ∈ [Reg.x0, .x2, .x4, .x5, .x6, .x7, .x8, .x9] := by decide

def aRegs : List Reg := [.x0, .x2, .x4, .x5, .x6, .x7, .x8, .x9]

theorem loadA_ok {s : State} {base : Addr} (hs : Scr s base) {a : Nat} (ha : a + 64 ≤ 8192)
    (ha8 : a % 8 = 0) :
    WP isa (.block (loadA a)) s fun t =>
      (∀ i < 8, t.gpr (Mul.A i) = word s.mem base (a + 8 * i)) ∧ t.mem = s.mem ∧
      Keeps VG.Proof.Curve448.AArch64.Fast.aRegs s t := by
  have e : loadA a = (List.range 8).flatMap fun i => [ld (Mul.A i) (a + 8 * i)] := by
    simp only [loadA]
    rfl
  rw [e]
  let inv := fun n (t : State) =>
    (∀ i < n, t.gpr (Mul.A i) = word s.mem base (a + 8 * i)) ∧ t.mem = s.mem ∧ Keeps VG.Proof.Curve448.AArch64.Fast.aRegs s t
  refine wp_range_flatMap (M := isa) (N := 8) inv (fun n t hn ⟨tv, tm, tk⟩ => ?_) 8 (by decide) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), rfl, Keeps.refl _ _⟩
  have ts : Scr t base := hs.of_keeps tk (by decide)
  refine WP.mono (VG.Proof.Curve448.AArch64.Fast.ld_ok ts (Mul.A n) (d := a + 8 * n) (by omega) (by omega)) fun u ⟨uv, um, uk⟩ => ?_
  refine ⟨fun i hi => ?_, um.trans tm, tk.trans (uk.mono fun r hr => ?_)⟩
  · by_cases h : i = n
    · subst h; rw [uv, tm]
    · have hne : Mul.A i ∉ [Mul.A n] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        exact VG.Proof.Curve448.AArch64.Fast.A_inj i (by omega) n hn h
      rw [uk.1 _ hne, tv i (by omega)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [hr]; exact VG.Proof.Curve448.AArch64.Fast.A_mem n hn

theorem consts_ok (s : State) :
    WP isa (.block consts) s fun t =>
      t.gpr MASK = BitVec.ofNat 64 (2 ^ 56 - 1) ∧ t.gpr ZERO = 0 ∧ t.mem = s.mem ∧
      Keeps [MASK, ZERO] s t := by
  refine WP.of_runBlock ⟨_, by
    simp only [consts, runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
      show 16 * 0 < 64 from by decide, show 16 * 1 < 64 from by decide,
      show 16 * 2 < 64 from by decide, show 16 * 3 < 64 from by decide, ite_true]; rfl, ?_⟩
  refine ⟨?_, ?_, rfl, fun q hq => ?_, rfl, rfl⟩
  · simp only [MASK, ZERO, State.read, RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false]
    decide
  · simp only [ZERO, RegUpd.gpr_write, ite_true]
    decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp only [RegUpd.gpr_write, hq.1, hq.2, ite_false]

theorem add_ok (s : State) (d n m : Reg) :
    WP isa (.block [.add .x d n m]) s fun t =>
      t.gpr d = s.gpr n + s.gpr m ∧ t.mem = s.mem ∧ Keeps [d] s t := by
  refine WP.of_runBlock ⟨_, by simp only [runBlock_cons, runStep_some, runBlock_nil, exec]; rfl, ?_⟩
  refine ⟨?_, rfl, fun q hq => ?_, rfl, rfl⟩
  · simp only [RegUpd.gpr_write, ite_true, read_x, BitVec.setWidth_eq]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    simp only [RegUpd.gpr_write, hq, ite_false]

theorem stw_ok {t : State} {base : Addr} (ht : Scr t base) (r : Reg) {d : Nat} (h8 : d % 8 = 0)
    (hd : d + 8 ≤ 8192) :
    WP isa (.block [st r d]) t fun t' =>
      (∀ d', d' + 8 ≤ 8192 → (d' = d ∨ d' + 8 ≤ d ∨ d + 8 ≤ d') →
        word t'.mem base d' = if d' = d then t.gpr r else word t.mem base d') ∧
      Outside base d 8 t.mem t'.mem ∧ t'.gpr = t.gpr ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  refine WP.mono (VG.Proof.Curve448.AArch64.Fast.st_ok ht r h8 hd) fun t' ⟨hm, hk⟩ => ⟨fun d' hd' hs => ?_, ?_, ?_, hk.2.1, hk.2.2⟩
  · rw [hm]; exact VG.Proof.Curve448.AArch64.Fast.word_writeW _ _ hd hd' hs _
  · rw [hm]; exact writeW_outside _ _ _ hd
  · funext q; exact hk.1 q (by simp)

theorem A_ne : ∀ i < 8, Mul.A i ∉ [Reg.x10, .x11, .x13] := by decide

/-- One step of the operand sums of a product. -/
theorem kakbStep_ok {s : State} {base : Addr} (hs : Scr s base) {b i : Nat} (hb : b + 64 ≤ ACC)
    (hb8 : b % 8 = 0) (hi : i < 4) :
    WP isa (.block [.add .x Mul.R.p0 (Mul.A i) (Mul.A (i + 4)), st Mul.R.p0 (KA + 8 * i),
      ld Mul.R.t (b + 8 * i), ld Mul.R.p1 (b + 32 + 8 * i),
      .add .x Mul.R.t Mul.R.t Mul.R.p1, st Mul.R.t (KB + 8 * i)]) s fun t =>
      word t.mem base (KA + 8 * i) = s.gpr (Mul.A i) + s.gpr (Mul.A (i + 4)) ∧
      word t.mem base (KB + 8 * i) = word s.mem base (b + 8 * i) + word s.mem base (b + 32 + 8 * i) ∧
      Outside base KA 64 s.mem t.mem ∧ Keeps [.x10, .x11, .x13] s t ∧
      (∀ d, d + 8 ≤ 8192 → (d + 8 ≤ KA + 8 * i ∨ KA + 8 * i + 8 ≤ d) →
        (d + 8 ≤ KB + 8 * i ∨ KB + 8 * i + 8 ≤ d) → word t.mem base d = word s.mem base d) := by
  have hA : ACC = 3584 := rfl
  have hKA : KA = ACC := rfl
  have hKB : KB = ACC + 32 := rfl
  rw [show [Instr.add .x Mul.R.p0 (Mul.A i) (Mul.A (i + 4)), st Mul.R.p0 (KA + 8 * i),
      ld Mul.R.t (b + 8 * i), ld Mul.R.p1 (b + 32 + 8 * i),
      .add .x Mul.R.t Mul.R.t Mul.R.p1, st Mul.R.t (KB + 8 * i)] =
      [Instr.add .x Mul.R.p0 (Mul.A i) (Mul.A (i + 4))] ++ [st Mul.R.p0 (KA + 8 * i)] ++
      [ld Mul.R.t (b + 8 * i)] ++ [ld Mul.R.p1 (b + 32 + 8 * i)] ++
      [Instr.add .x Mul.R.t Mul.R.t Mul.R.p1] ++ [st Mul.R.t (KB + 8 * i)] from rfl]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Curve448.AArch64.Fast.add_ok s _ _ _) fun t1 ⟨v1, m1, k1⟩ => ?_
  have s1 : Scr t1 base := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Curve448.AArch64.Fast.stw_ok s1 _ (d := KA + 8 * i) (by omega) (by omega)) fun t2 ⟨w2, o2, g2, r2, wr2⟩ => ?_
  have s2 : Scr t2 base := ⟨by rw [g2]; exact s1.x3, by rw [g2]; exact s1.mask, wr2 ▸ s1.wr, s1.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Curve448.AArch64.Fast.ld_ok s2 Mul.R.t (d := b + 8 * i) (by omega) (by omega)) fun t3 ⟨v3, m3, k3⟩ => ?_
  have s3 : Scr t3 base := s2.of_keeps k3 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Curve448.AArch64.Fast.ld_ok s3 Mul.R.p1 (d := b + 32 + 8 * i) (by omega) (by omega)) fun t4 ⟨v4, m4, k4⟩ => ?_
  have s4 : Scr t4 base := s3.of_keeps k4 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Curve448.AArch64.Fast.add_ok t4 _ _ _) fun t5 ⟨v5, m5, k5⟩ => ?_
  have s5 : Scr t5 base := s4.of_keeps k5 (by decide)
  refine WP.mono (VG.Proof.Curve448.AArch64.Fast.stw_ok s5 _ (d := KB + 8 * i) (by omega) (by omega)) fun t6 ⟨w6, o6, g6, r6, wr6⟩ => ?_
  have hb1 : word t2.mem base (b + 8 * i) = word s.mem base (b + 8 * i) := by
    rw [w2 _ (by omega) (by omega), ite_eq_right (by omega), m1]
  have hb2 : word t2.mem base (b + 32 + 8 * i) = word s.mem base (b + 32 + 8 * i) := by
    rw [w2 _ (by omega) (by omega), ite_eq_right (by omega), m1]
  refine ⟨?_, ?_, ?_, ?_, fun d hd h1 h2 => ?_⟩
  · rw [w6 _ (by omega) (by omega), ite_eq_right (by omega), m5, m4, m3, w2 _ (by omega) (by omega),
      ite_eq_left rfl, v1]
  · rw [w6 _ (by omega) (by omega), ite_eq_left rfl, v5, k4.1 Mul.R.t (by decide), v3, v4, m3, hb1, hb2]
  · rw [← m1]
    refine (o2.mono (by omega) (by omega)).trans ?_
    rw [← m3, ← m4, ← m5]
    exact o6.mono (by omega) (by omega)
  · refine ⟨fun q hq => ?_, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
      rw [g6, k5.1 q (by simp [Mul.R, hq.1]), k4.1 q (by simp [Mul.R, hq.2.1]),
        k3.1 q (by simp [Mul.R, hq.1]), g2, k1.1 q (by simp [Mul.R, hq.2.2])]
    · rw [r6, k5.2.1, k4.2.1, k3.2.1, r2, k1.2.1]
    · rw [wr6, k5.2.2, k4.2.2, k3.2.2, wr2, k1.2.2]
  · rw [w6 _ hd (by omega), ite_eq_right (by omega), m5, m4, m3, w2 _ hd (by omega),
      ite_eq_right (by omega), m1]

end VG.Proof.Curve448.AArch64.Fast

end

/- Proofs formerly in `VerifiedGarbage.Proof.Curve448.AArch64.Fast.Loop`. -/
section

/-!
# The four columns of a product

Untrusted: everything here is checked by Lean. For any registers and steps
whose accumulators `L` and `H` hold coefficients `d` and `d + 4` of `r` after
column `d` (`hsem`), the columns stage the limbs of both carry chains and
leave their last carries in `CL` and `CH`.
-/

namespace VG.Proof.Curve448.AArch64.Fast

open VG VG.AArch64
open VG.Impl.Curve448.AArch64.Fast
open VG.Impl.X448.AArch64 (ld st ACC)
open VG.Proof.X448.Wide (radix pair)
open VG.Proof.X448.AArch64 (Keeps Scr word off Outside writeW_outside limbs)

/-- The registers a column may write. -/
def colWrites (R : Regs) (accs : List Acc) : List Reg := VG.Proof.Curve448.AArch64.Fast.writes R accs ++ [CL, CH]

/-- What the columns guarantee after `n` of them. -/
structure ColInv (base : Addr) (o : Nat) (r : Nat → Nat) (s t : State) (n : Nat) : Prop where
  scr : Scr t base
  mask : t.gpr MASK = BitVec.ofNat 64 (2 ^ 56 - 1)
  zero : t.gpr ZERO = 0
  out : Outside base o 64 s.mem t.mem
  lo : ∀ k < n, (word t.mem base (o + 8 * k)).toNat = VG.Proof.Curve448.AArch64.Fast.chainLimb r 0 k
  hi : ∀ k < n, (word t.mem base (o + 8 * (4 + k))).toNat = VG.Proof.Curve448.AArch64.Fast.chainLimb r 4 k
  cl : 0 < n → (t.gpr CL).toNat = VG.Proof.Curve448.AArch64.Fast.chain r 0 n
  ch : 0 < n → (t.gpr CH).toNat = VG.Proof.Curve448.AArch64.Fast.chain r 4 n

theorem colEnd_ok {s : State} {base : Addr} (hs : Scr s base) (t : Reg) (a : Acc) (c : Reg)
    (first : Bool) {o k : Nat} (ho8 : o % 8 = 0) (ho : o + 64 ≤ 8192) (hk : k < 8) (h₁ : t ≠ a.lo) (h₂ : t ≠ a.hi) (h₃ : t ≠ .x3)
    (h₄ : a.lo ≠ a.hi) (h₅ : a.lo ≠ ZERO) (h₆ : MASK ∉ [a.lo, a.hi]) (h₇ : a.lo ≠ .x3)
    (h₈ : a.hi ≠ .x3) (h₉ : a.lo ≠ .x12) (h₁₀ : a.hi ≠ .x12)
    (hm : s.gpr MASK = BitVec.ofNat 64 (2 ^ 56 - 1)) (hz : s.gpr ZERO = 0)
    {V cin : Nat} (hV : VG.Proof.Curve448.AArch64.Fast.accVal s a = V) (hc : first = false → (s.gpr c).toNat = cin)
    (h0 : first = true → cin = 0) (hlt : V + cin < 2 ^ 120) :
    WP isa (.block (colEnd t a c first o k)) s fun u =>
      u.mem = s.mem.writeW (off base (o + 8 * k)) (BitVec.ofNat 64 ((V + cin) % VG.Proof.X448.Wide.radix)) ∧
      (u.gpr c).toNat = (V + cin) / VG.Proof.X448.Wide.radix ∧ Keeps [a.lo, a.hi, t, c] s u := by
  cases first
  · simp only [colEnd, Bool.false_eq_true, ite_false, List.cons_append, List.nil_append]
    rw [show (Instr.adds .x a.lo a.lo c :: Instr.adc .x a.hi a.hi ZERO ::
        [Instr.logic .and .x t a.lo MASK, st t (o + 8 * k), .extr .x c a.hi a.lo 56]) =
        [Instr.adds .x a.lo a.lo c, .adc .x a.hi a.hi ZERO] ++
        [Instr.logic .and .x t a.lo MASK, st t (o + 8 * k), .extr .x c a.hi a.lo 56] from rfl,
      WP.block_append_iff]
    have hc' := hc rfl
    refine WP.mono (VG.Proof.Curve448.AArch64.Fast.carryIn_ok s a c h₄ h₅ hz (by rw [hV, hc']; omega)) fun u ⟨uv, um, uk⟩ => ?_
    have us : Scr u base := hs.of_keeps uk (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨⟨Ne.symm h₇, Ne.symm h₈⟩, ⟨Ne.symm h₉, Ne.symm h₁₀⟩⟩)
    have um' : u.gpr MASK = BitVec.ofNat 64 (2 ^ 56 - 1) := by rw [uk.1 _ h₆, hm]
    refine WP.mono (VG.Proof.Curve448.AArch64.Fast.stage_ok us t a c (by omega) (by omega) h₁ h₂ h₃ um' (by rw [uv, hV, hc']; omega))
      fun w ⟨wm, wc, wk⟩ => ⟨?_, ?_, ?_⟩
    · rw [wm, uv, um, hV, hc']
    · rw [wc, uv, hV, hc']
    · refine (uk.mono ?_).trans (wk.mono ?_) <;> intro r hr <;>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢ <;>
        rcases hr with h | h <;> simp [h]
  · simp only [colEnd, ite_true, List.nil_append]
    have hc' := h0 rfl
    subst hc'
    refine WP.mono (VG.Proof.Curve448.AArch64.Fast.stage_ok hs t a c (by omega) (by omega) h₁ h₂ h₃ hm (by rw [hV]; omega))
      fun w ⟨wm, wc, wk⟩ => ⟨?_, ?_, ?_⟩
    · rw [wm, hV, Nat.add_zero]
    · rw [wc, hV, Nat.add_zero]
    · refine wk.mono ?_
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h <;> simp [h]

/-- The carry and constant registers are not written by the steps, by `decide`. -/
abbrev ColRegs (R : Regs) (accs : List Acc) : Prop :=
  MASK ∉ VG.Proof.Curve448.AArch64.Fast.colWrites R accs ∧ ZERO ∉ VG.Proof.Curve448.AArch64.Fast.colWrites R accs ∧ CL ∉ VG.Proof.Curve448.AArch64.Fast.writes R accs ∧ CH ∉ VG.Proof.Curve448.AArch64.Fast.writes R accs ∧
  CL ≠ CH ∧ Reg.x3 ∉ [CL, CH] ∧ Reg.x12 ∉ [CL, CH]

theorem word_stage {m : Mem} {base : Addr} {o k j : Nat} (ho : o + 64 ≤ 8192) (hk : k < 8)
    (hj : j < 8) (v : BitVec 64) :
    word (m.writeW (off base (o + 8 * k)) v) base (o + 8 * j) =
      if j = k then v else word m base (o + 8 * j) := by
  rw [VG.Proof.Curve448.AArch64.Fast.word_writeW m base (by omega) (by omega) (by omega)]
  by_cases h : j = k
  · rw [ite_eq_left (by omega), ite_eq_left h]
  · rw [ite_eq_right (by omega), ite_eq_right h]

theorem stage_outside (m : Mem) (base : Addr) {o k : Nat} (ho : o + 64 ≤ 8192) (hk : k < 8)
    (v : BitVec 64) : Outside base o 64 m (m.writeW (off base (o + 8 * k)) v) := by
  exact (writeW_outside m base v (by omega)).mono (by omega) (by omega)

section
variable {R : Regs} {accs : List Acc} {L H : Acc} {col : Nat → List MOp} {b o : Nat}
  {r : Nat → Nat} {base : Addr}

theorem column_ok (hG : VG.Proof.Curve448.AArch64.Fast.Good R accs) (hC : VG.Proof.Curve448.AArch64.Fast.ColRegs R accs) (hL : L ∈ accs) (hH : H ∈ accs)
    (hLH : L ≠ H) (hb8 : b % 8 = 0) (hb : b + 64 ≤ 8192) (ho8 : o % 8 = 0) (ho : o + 64 ≤ 8192)
    (hfit : VG.Proof.Curve448.AArch64.Fast.Fits r) {d : Nat} (hd : d < 4) (hops : (col d).all (VG.Proof.Curve448.AArch64.Fast.opOk (VG.Proof.Curve448.AArch64.Fast.writes R accs) accs) = true)
    {t : State} {s : State} (hi : VG.Proof.Curve448.AArch64.Fast.ColInv base o r s t d)
    (hsem : ∀ e, VG.Proof.Curve448.AArch64.Fast.sem (VG.Proof.Curve448.AArch64.Fast.srcVal t base b) e (col d) L = r d ∧ VG.Proof.Curve448.AArch64.Fast.sem (VG.Proof.Curve448.AArch64.Fast.srcVal t base b) e (col d) H = r (d + 4)) :
    WP isa (.block ((col d).flatMap (MOp.code R b) ++ colEnd R.t L CL (d == 0) o d ++
        colEnd R.t H CH (d == 0) o (d + 4))) t fun w =>
      VG.Proof.Curve448.AArch64.Fast.ColInv base o r s w (d + 1) ∧ Keeps (VG.Proof.Curve448.AArch64.Fast.colWrites R accs) t w ∧ Outside base o 64 t.mem w.mem := by
  obtain ⟨hM, hZ, hCL, hCH, hCC, h3, h12⟩ := hC
  have nM : MASK ∉ VG.Proof.Curve448.AArch64.Fast.writes R accs := fun h => hM (List.mem_append_left _ h)
  have nZ : ZERO ∉ VG.Proof.Curve448.AArch64.Fast.writes R accs := fun h => hZ (List.mem_append_left _ h)
  obtain ⟨Llh, Llo, Lhi⟩ := hG.acc hL
  obtain ⟨Hlh, Hlo, Hhi⟩ := hG.acc hH
  have x3w : Reg.x3 ∉ VG.Proof.Curve448.AArch64.Fast.writes R accs := hG.2.2.2.2.2.1
  have x12w : Reg.x12 ∉ VG.Proof.Curve448.AArch64.Fast.writes R accs := hG.2.2.2.2.2.2
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.Curve448.AArch64.Fast.mops_ok hG hb8 hb (col d) hops hi.scr (v := VG.Proof.Curve448.AArch64.Fast.srcVal t base b) (fun _ _ => rfl)
    (e := fun a => (VG.Proof.Curve448.AArch64.Fast.accVal t a : Int)) (fun a _ => VG.Proof.Curve448.AArch64.Fast.self_emod (VG.Proof.Curve448.AArch64.Fast.pair_lt _ _))) fun u ⟨uv, um, uk⟩ => ?_
  have us : Scr u base := hG.scr hi.scr uk (fun _ h => h)
  obtain ⟨sL, sH⟩ := hsem (fun a => (VG.Proof.Curve448.AArch64.Fast.accVal t a : Int))
  have rL : VG.Proof.Curve448.AArch64.Fast.accVal u L = r d := VG.Proof.Curve448.AArch64.Fast.exact_of_emod (uv L hL) sL (by
    have := hfit.low d hd; simp only [VG.Proof.Curve448.AArch64.Fast.M]; omega)
  have rH : VG.Proof.Curve448.AArch64.Fast.accVal u H = r (4 + d) := VG.Proof.Curve448.AArch64.Fast.exact_of_emod (uv H hH) (by rw [sH, Nat.add_comm]) (by
    have := hfit.high d hd; simp only [VG.Proof.Curve448.AArch64.Fast.M]; omega)
  have um' : u.gpr MASK = BitVec.ofNat 64 (2 ^ 56 - 1) := by rw [uk.1 _ nM, hi.mask]
  have uz : u.gpr ZERO = 0 := by rw [uk.1 _ nZ, hi.zero]
  have tne : ∀ a ∈ accs, R.t ≠ a.lo ∧ R.t ≠ a.hi := fun a ha => by
    obtain ⟨-, h1, h2⟩ := hG.acc ha
    exact ⟨fun e => h1 (by simp [e]), fun e => h2 (by simp [e])⟩
  have t3 : R.t ≠ .x3 := fun e => x3w (e ▸ VG.Proof.Curve448.AArch64.Fast.t_mem)
  have nmem : ∀ {q : Reg} {a : Acc}, a ∈ accs → q ∉ VG.Proof.Curve448.AArch64.Fast.writes R accs → q ∉ [a.lo, a.hi] := by
    intro q a ha hq hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h | h
    · exact hq (h ▸ VG.Proof.Curve448.AArch64.Fast.lo_mem ha)
    · exact hq (h ▸ VG.Proof.Curve448.AArch64.Fast.hi_mem ha)
  rw [WP.block_append_iff]
  have hcL : (d == 0) = false → (u.gpr CL).toNat = VG.Proof.Curve448.AArch64.Fast.chain r 0 d := fun h => by
    rw [uk.1 _ hCL]; exact hi.cl (by simp at h; omega)
  have h0L : (d == 0) = true → VG.Proof.Curve448.AArch64.Fast.chain r 0 d = 0 := fun h => by
    simp at h; subst h; rfl
  refine WP.mono (VG.Proof.Curve448.AArch64.Fast.colEnd_ok us R.t L CL (d == 0) (k := d) ho8 ho (by omega) (tne L hL).1 (tne L hL).2 t3 Llh
    (fun e => nZ (e ▸ VG.Proof.Curve448.AArch64.Fast.lo_mem hL)) (nmem hL nM) (fun e => x3w (e ▸ VG.Proof.Curve448.AArch64.Fast.lo_mem hL))
    (fun e => x3w (e ▸ VG.Proof.Curve448.AArch64.Fast.hi_mem hL)) (fun e => x12w (e ▸ VG.Proof.Curve448.AArch64.Fast.lo_mem hL)) (fun e => x12w (e ▸ VG.Proof.Curve448.AArch64.Fast.hi_mem hL))
    um' uz rL hcL h0L (hfit.low d hd)) fun w ⟨wm, wc, wk⟩ => ?_
  have lnot : ∀ {q : Reg}, q ∉ VG.Proof.Curve448.AArch64.Fast.writes R accs → q ≠ CL → q ∉ [L.lo, L.hi, R.t, CL] := by
    intro q hq hc hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h | h | h | h
    · exact hq (h ▸ VG.Proof.Curve448.AArch64.Fast.lo_mem hL)
    · exact hq (h ▸ VG.Proof.Curve448.AArch64.Fast.hi_mem hL)
    · exact hq (h ▸ VG.Proof.Curve448.AArch64.Fast.t_mem)
    · exact hc h
  have ws : Scr w base := us.of_keeps wk (by
    refine ⟨lnot x3w (fun e => h3 (by simp [e])), lnot x12w (fun e => h12 (by simp [e]))⟩)
  have wM : w.gpr MASK = BitVec.ofNat 64 (2 ^ 56 - 1) := by
    rw [wk.1 _ (lnot nM (fun e => hM (by simp [VG.Proof.Curve448.AArch64.Fast.colWrites, e]))), um']
  have wZ : w.gpr ZERO = 0 := by
    rw [wk.1 _ (lnot nZ (fun e => hZ (by simp [VG.Proof.Curve448.AArch64.Fast.colWrites, e]))), uz]
  have wH : VG.Proof.Curve448.AArch64.Fast.accVal w H = r (4 + d) := by
    obtain ⟨d1, d2⟩ := hG.disj hH hL (Ne.symm hLH)
    rw [VG.Proof.Curve448.AArch64.Fast.accVal_keep wk (fun e => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at e
        rcases e with e | e | e | e
        · exact d1 (by simp [e])
        · exact d1 (by simp [e])
        · exact (tne H hH).1 e.symm
        · exact hCL (e ▸ VG.Proof.Curve448.AArch64.Fast.lo_mem hH))
      (fun e => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at e
        rcases e with e | e | e | e
        · exact d2 (by simp [e])
        · exact d2 (by simp [e])
        · exact (tne H hH).2 e.symm
        · exact hCL (e ▸ VG.Proof.Curve448.AArch64.Fast.hi_mem hH)), rH]
  have hcH : (d == 0) = false → (w.gpr CH).toNat = VG.Proof.Curve448.AArch64.Fast.chain r 4 d := fun h => by
    rw [wk.1 _ (lnot hCH (Ne.symm hCC)), uk.1 _ hCH]; exact hi.ch (by simp at h; omega)
  have h0H : (d == 0) = true → VG.Proof.Curve448.AArch64.Fast.chain r 4 d = 0 := fun h => by
    simp at h; subst h; rfl
  refine WP.mono (VG.Proof.Curve448.AArch64.Fast.colEnd_ok ws R.t H CH (d == 0) (k := d + 4) ho8 ho (by omega) (tne H hH).1 (tne H hH).2 t3
    Hlh (fun e => nZ (e ▸ VG.Proof.Curve448.AArch64.Fast.lo_mem hH)) (nmem hH nM) (fun e => x3w (e ▸ VG.Proof.Curve448.AArch64.Fast.lo_mem hH))
    (fun e => x3w (e ▸ VG.Proof.Curve448.AArch64.Fast.hi_mem hH)) (fun e => x12w (e ▸ VG.Proof.Curve448.AArch64.Fast.lo_mem hH)) (fun e => x12w (e ▸ VG.Proof.Curve448.AArch64.Fast.hi_mem hH))
    wM wZ wH hcH h0H (hfit.high d hd)) fun x ⟨xm, xc, xk⟩ => ?_
  have hnot : ∀ {q : Reg}, q ∉ VG.Proof.Curve448.AArch64.Fast.writes R accs → q ≠ CH → q ∉ [H.lo, H.hi, R.t, CH] := by
    intro q hq hc hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h | h | h | h
    · exact hq (h ▸ VG.Proof.Curve448.AArch64.Fast.lo_mem hH)
    · exact hq (h ▸ VG.Proof.Curve448.AArch64.Fast.hi_mem hH)
    · exact hq (h ▸ VG.Proof.Curve448.AArch64.Fast.t_mem)
    · exact hc h
  have rad : ∀ n, n % VG.Proof.X448.Wide.radix < 2 ^ 64 := fun n => Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)
  have tw : Outside base o 64 t.mem x.mem := by
    rw [xm, wm, um]
    exact (VG.Proof.Curve448.AArch64.Fast.stage_outside _ _ ho (by omega) _).trans (VG.Proof.Curve448.AArch64.Fast.stage_outside _ _ ho (by omega) _)
  have sub : ∀ q ∈ VG.Proof.Curve448.AArch64.Fast.writes R accs, q ∈ VG.Proof.Curve448.AArch64.Fast.colWrites R accs := fun q h => List.mem_append_left _ h
  refine ⟨⟨ws.of_keeps xk ⟨hnot x3w (fun e => h3 (by simp [e])), hnot x12w (fun e => h12 (by simp [e]))⟩,
    by rw [xk.1 _ (hnot nM (fun e => hM (by simp [VG.Proof.Curve448.AArch64.Fast.colWrites, e]))), wM],
    by rw [xk.1 _ (hnot nZ (fun e => hZ (by simp [VG.Proof.Curve448.AArch64.Fast.colWrites, e]))), wZ],
    hi.out.trans tw, fun k hk => ?_, fun k hk => ?_, fun _ => ?_, fun _ => ?_⟩,
    (uk.mono sub).trans ((wk.mono ?_).trans (xk.mono ?_)), tw⟩
  · rw [xm, VG.Proof.Curve448.AArch64.Fast.word_stage ho (by omega) (by omega), ite_eq_right (by omega), wm, VG.Proof.Curve448.AArch64.Fast.word_stage ho (by omega) (by omega)]
    by_cases h : k = d
    · rw [ite_eq_left h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (rad _), h]
      simp only [VG.Proof.Curve448.AArch64.Fast.chainLimb, Nat.zero_add]
    · rw [ite_eq_right h, um]; exact hi.lo k (by omega)
  · rw [xm, show 4 + k = k + 4 by omega, VG.Proof.Curve448.AArch64.Fast.word_stage ho (by omega) (by omega)]
    by_cases h : k + 4 = d + 4
    · rw [ite_eq_left h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (rad _), show k = d by omega]
      simp only [VG.Proof.Curve448.AArch64.Fast.chainLimb]
    · rw [ite_eq_right h, wm, VG.Proof.Curve448.AArch64.Fast.word_stage ho (by omega) (by omega), ite_eq_right (by omega), um,
        show k + 4 = 4 + k by omega]
      exact hi.hi k (by omega)
  · rw [xk.1 _ (hnot hCL hCC), wc]
    simp only [VG.Proof.Curve448.AArch64.Fast.chain, Nat.zero_add]
  · rw [xc]
    simp only [VG.Proof.Curve448.AArch64.Fast.chain]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with h | h | h | h
    · exact sub _ (h ▸ VG.Proof.Curve448.AArch64.Fast.lo_mem hL)
    · exact sub _ (h ▸ VG.Proof.Curve448.AArch64.Fast.hi_mem hL)
    · exact sub _ (h ▸ VG.Proof.Curve448.AArch64.Fast.t_mem)
    · rw [h]; simp [VG.Proof.Curve448.AArch64.Fast.colWrites]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with h | h | h | h
    · exact sub _ (h ▸ VG.Proof.Curve448.AArch64.Fast.lo_mem hH)
    · exact sub _ (h ▸ VG.Proof.Curve448.AArch64.Fast.hi_mem hH)
    · exact sub _ (h ▸ VG.Proof.Curve448.AArch64.Fast.t_mem)
    · rw [h]; simp [VG.Proof.Curve448.AArch64.Fast.colWrites]

theorem columns_ok (hG : VG.Proof.Curve448.AArch64.Fast.Good R accs) (hC : VG.Proof.Curve448.AArch64.Fast.ColRegs R accs) (hL : L ∈ accs) (hH : H ∈ accs)
    (hLH : L ≠ H) (hb8 : b % 8 = 0) (hb : b + 64 ≤ 8192) (ho8 : o % 8 = 0) (ho : o + 64 ≤ 8192)
    (hfit : VG.Proof.Curve448.AArch64.Fast.Fits r) (hops : ∀ d < 4, (col d).all (VG.Proof.Curve448.AArch64.Fast.opOk (VG.Proof.Curve448.AArch64.Fast.writes R accs) accs) = true)
    (P : State → Prop)
    (hP : ∀ t u, P t → Keeps (VG.Proof.Curve448.AArch64.Fast.colWrites R accs) t u → Outside base o 64 t.mem u.mem → P u)
    (hsem : ∀ d < 4, ∀ t, P t → ∀ e,
      VG.Proof.Curve448.AArch64.Fast.sem (VG.Proof.Curve448.AArch64.Fast.srcVal t base b) e (col d) L = r d ∧ VG.Proof.Curve448.AArch64.Fast.sem (VG.Proof.Curve448.AArch64.Fast.srcVal t base b) e (col d) H = r (d + 4))
    {s : State} (hs : Scr s base) (hP0 : P s) (hm : s.gpr MASK = BitVec.ofNat 64 (2 ^ 56 - 1))
    (hz : s.gpr ZERO = 0) :
    WP isa (.block (columns R b L H col o)) s fun t =>
      P t ∧ VG.Proof.Curve448.AArch64.Fast.ColInv base o r s t 4 ∧ Keeps (VG.Proof.Curve448.AArch64.Fast.colWrites R accs) s t := by
  let inv := fun n (t : State) => P t ∧ VG.Proof.Curve448.AArch64.Fast.ColInv base o r s t n ∧ Keeps (VG.Proof.Curve448.AArch64.Fast.colWrites R accs) s t
  refine wp_range_flatMap (M := isa) (N := 4) inv (fun n t hn ⟨tp, ti, tk⟩ => ?_) 4 (by decide) s
    ⟨hP0, ⟨hs, hm, hz, Outside.refl _ _ _ _, fun _ h => absurd h (Nat.not_lt_zero _),
      fun _ h => absurd h (Nat.not_lt_zero _), fun h => absurd h (Nat.lt_irrefl _),
      fun h => absurd h (Nat.lt_irrefl _)⟩, Keeps.refl _ _⟩
  exact WP.mono (VG.Proof.Curve448.AArch64.Fast.column_ok hG hC hL hH hLH hb8 hb ho8 ho hfit hn (hops n hn) ti (hsem n hn t tp))
    fun u ⟨ui, uk, uo⟩ => ⟨hP t u tp uk uo, ui, tk.trans uk⟩

end

end VG.Proof.Curve448.AArch64.Fast

end

/- Proofs formerly in `VerifiedGarbage.Proof.Curve448.AArch64.Fast.Columns`. -/
section

/-!
# Karatsuba's columns are the reduced product's coefficients

Untrusted: everything here is checked by Lean. For each column `d < 4` of a
multiplication (or a square), the signed sums of products that `sem`
accumulates in `L` and `H` are the coefficients `d` and `d + 4` of the
schoolbook product folded with `2⁴⁴⁸ = 2²²⁴ + 1`, `reduced (rows f g 8)`.
-/

namespace VG.Proof.Curve448.AArch64.Fast

open VG VG.AArch64
open VG.Impl.Curve448.AArch64.Fast
open VG.Proof.X448.Wide (rows reduced addRow addRow_at addAt)

theorem pairs_0 : pairs 0 = [(0, 0)] := by decide
theorem pairs_1 : pairs 1 = [(0, 1), (1, 0)] := by decide
theorem pairs_2 : pairs 2 = [(0, 2), (1, 1), (2, 0)] := by decide
theorem pairs_3 : pairs 3 = [(0, 3), (1, 2), (2, 1), (3, 0)] := by decide
theorem pairs_4 : pairs 4 = [(1, 3), (2, 2), (3, 1)] := by decide
theorem pairs_5 : pairs 5 = [(2, 3), (3, 2)] := by decide
theorem pairs_6 : pairs 6 = [(3, 3)] := by decide
theorem pairs_7 : pairs 7 = [] := by decide

theorem sqPairs_0 : sqPairs 0 = [(0, 0)] := by decide
theorem sqPairs_1 : sqPairs 1 = [(0, 1)] := by decide
theorem sqPairs_2 : sqPairs 2 = [(0, 2), (1, 1)] := by decide
theorem sqPairs_3 : sqPairs 3 = [(0, 3), (1, 2)] := by decide
theorem sqPairs_4 : sqPairs 4 = [(1, 3), (2, 2)] := by decide
theorem sqPairs_5 : sqPairs 5 = [(2, 3)] := by decide
theorem sqPairs_6 : sqPairs 6 = [(3, 3)] := by decide
theorem sqPairs_7 : sqPairs 7 = [] := by decide

/-- The schoolbook coefficients, one sum per diagonal. -/
theorem rows_eq (f g : Nat → Nat) (k : Nat) :
    VG.Proof.X448.Wide.rows f g 8 k = (if k < 8 then f 0 * g k else 0) +
      (if 1 ≤ k ∧ k < 9 then f 1 * g (k - 1) else 0) +
      (if 2 ≤ k ∧ k < 10 then f 2 * g (k - 2) else 0) +
      (if 3 ≤ k ∧ k < 11 then f 3 * g (k - 3) else 0) +
      (if 4 ≤ k ∧ k < 12 then f 4 * g (k - 4) else 0) +
      (if 5 ≤ k ∧ k < 13 then f 5 * g (k - 5) else 0) +
      (if 6 ≤ k ∧ k < 14 then f 6 * g (k - 6) else 0) +
      (if 7 ≤ k ∧ k < 15 then f 7 * g (k - 7) else 0) := by
  simp only [VG.Proof.X448.Wide.rows, VG.Proof.X448.Wide.addRow_at]
  simp only [Nat.zero_add, Nat.zero_le, true_and, Nat.sub_zero]

section Mul
open Mul

variable (f g : Nat → Nat) (v : Src → Nat)
  (h0 : ∀ i j, i < 4 → j < 4 → (v (src 0 (i, j)).1 : Int) * v (src 0 (i, j)).2 = f i * g j)
  (h1 : ∀ i j, i < 4 → j < 4 → (v (src 1 (i, j)).1 : Int) * v (src 1 (i, j)).2 = f (i + 4) * g (j + 4))
  (h2 : ∀ i j, i < 4 → j < 4 → (v (src 2 (i, j)).1 : Int) * v (src 2 (i, j)).2 =
    (f i + f (i + 4)) * (g j + g (j + 4)))
include h0 h1 h2

theorem mulCol_ok (e : VG.Proof.Curve448.AArch64.Fast.Env) {d : Nat} (hd : d < 4) :
    VG.Proof.Curve448.AArch64.Fast.sem v e (column d) VG.Impl.Curve448.AArch64.Fast.Mul.L = VG.Proof.X448.Wide.reduced (VG.Proof.X448.Wide.rows f g 8) d ∧
    VG.Proof.Curve448.AArch64.Fast.sem v e (column d) H = VG.Proof.X448.Wide.reduced (VG.Proof.X448.Wide.rows f g 8) (d + 4) := by
  obtain rfl | rfl | rfl | rfl : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
  all_goals
    simp (config := {decide := true}) only [column, terms, Nat.reduceAdd, VG.Proof.Curve448.AArch64.Fast.pairs_0, VG.Proof.Curve448.AArch64.Fast.pairs_1,
      VG.Proof.Curve448.AArch64.Fast.pairs_2, VG.Proof.Curve448.AArch64.Fast.pairs_3, VG.Proof.Curve448.AArch64.Fast.pairs_4, VG.Proof.Curve448.AArch64.Fast.pairs_5, VG.Proof.Curve448.AArch64.Fast.pairs_6, VG.Proof.Curve448.AArch64.Fast.pairs_7, start, addTo, shared,
      List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, List.append_nil, VG.Proof.Curve448.AArch64.Fast.sem, VG.Proof.Curve448.AArch64.Fast.opSem, List.foldl, VG.Proof.Curve448.AArch64.Fast.target, VG.Proof.Curve448.AArch64.Fast.upd, ite_true, ite_false,
      h0, h1, h2]
    simp only [VG.Proof.X448.Wide.reduced, VG.Proof.Curve448.AArch64.Fast.rows_eq, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceLeDiff,
      and_true, and_false, and_self, ite_true, ite_false, Nat.add_zero,
      Nat.zero_add]
    constructor <;> (push_cast; simp only [Int.add_mul, Int.mul_add, Int.mul_comm]; omega)

end Mul

section Sqr
open Sqr

variable (f : Nat → Nat) (v : Src → Nat)
  (h0 : ∀ i j, i ≤ j → j < 4 → (v (src 0 (i, j)).1 : Int) * v (src 0 (i, j)).2 =
    (if i = j then 1 else 2) * f i * f j)
  (h1 : ∀ i j, i ≤ j → j < 4 → (v (src 1 (i, j)).1 : Int) * v (src 1 (i, j)).2 =
    (if i = j then 1 else 2) * f (i + 4) * f (j + 4))
  (h2 : ∀ i j, i ≤ j → j < 4 → (v (src 2 (i, j)).1 : Int) * v (src 2 (i, j)).2 =
    (if i = j then 1 else 2) * (f i + f (i + 4)) * (f j + f (j + 4)))
include h0 h1 h2

theorem sqrCol_ok (e : VG.Proof.Curve448.AArch64.Fast.Env) {d : Nat} (hd : d < 4) :
    VG.Proof.Curve448.AArch64.Fast.sem v e (column d) VG.Impl.Curve448.AArch64.Fast.Sqr.L = VG.Proof.X448.Wide.reduced (VG.Proof.X448.Wide.rows f f 8) d ∧
    VG.Proof.Curve448.AArch64.Fast.sem v e (column d) H = VG.Proof.X448.Wide.reduced (VG.Proof.X448.Wide.rows f f 8) (d + 4) := by
  obtain rfl | rfl | rfl | rfl : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
  all_goals
    simp (config := {decide := true}) only [column, terms, Nat.reduceAdd, VG.Proof.Curve448.AArch64.Fast.sqPairs_0, VG.Proof.Curve448.AArch64.Fast.sqPairs_1,
      VG.Proof.Curve448.AArch64.Fast.sqPairs_2, VG.Proof.Curve448.AArch64.Fast.sqPairs_3, VG.Proof.Curve448.AArch64.Fast.sqPairs_4, VG.Proof.Curve448.AArch64.Fast.sqPairs_5, VG.Proof.Curve448.AArch64.Fast.sqPairs_6, VG.Proof.Curve448.AArch64.Fast.sqPairs_7, start, addTo,
      List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, List.append_nil, VG.Proof.Curve448.AArch64.Fast.sem, VG.Proof.Curve448.AArch64.Fast.opSem, List.foldl, VG.Proof.Curve448.AArch64.Fast.target, VG.Proof.Curve448.AArch64.Fast.upd, ite_true, ite_false,
      h0, h1, h2]
    simp only [VG.Proof.X448.Wide.reduced, VG.Proof.Curve448.AArch64.Fast.rows_eq, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceLeDiff,
      and_true, and_false, and_self, ite_true, ite_false, Nat.add_zero,
      Nat.zero_add]
    constructor <;> (push_cast; simp only [Int.add_mul, Int.mul_add, Int.mul_assoc, Int.mul_comm,
      Int.mul_left_comm, Int.one_mul]; omega)

end Sqr

end VG.Proof.Curve448.AArch64.Fast

end

/- Proofs formerly in `VerifiedGarbage.Proof.Curve448.AArch64.Fast.Mul`. -/
section

/-!
# Multiplication

Untrusted: everything here is checked by Lean. `mul o a b` writes the
limbs `out r` of the reduced schoolbook coefficients `r` of `[a] * [b]` to
`o`, for operand limbs below `Ib`.
-/

namespace VG.Proof.Curve448.AArch64.Fast

open VG VG.AArch64
open VG.Impl.Curve448.AArch64.Fast
open VG.Impl.X448.AArch64 (ld st ACC)
open VG.Proof.X448.Wide (radix pair rows reduced)
open VG.Proof.X448.AArch64 (Keeps Scr word off Outside writeW_outside limbs FieldMem ofs)

/-- The registers every field operation may write. -/
def clob : List Reg :=
  [.x0, .x2, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x13, .x14, .x15, .x16, .x17,
    .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28]

def kakb (b : Nat) : List Instr :=
  (List.range 4).flatMap (fun i =>
    [.add .x Mul.R.p0 (Mul.A i) (Mul.A (i + 4)), st Mul.R.p0 (KA + 8 * i),
      ld Mul.R.t (b + 8 * i), ld Mul.R.p1 (b + 32 + 8 * i),
      .add .x Mul.R.t Mul.R.t Mul.R.p1, st Mul.R.t (KB + 8 * i)])

theorem mul_split (o a b : Nat) :
    mul o a b = loadA a ++ consts ++ VG.Proof.Curve448.AArch64.Fast.kakb b ++ columns Mul.R b Mul.L Mul.H Mul.column o ++ finish o :=
  rfl

theorem kakb_ok {s : State} {base : Addr} (hs : Scr s base) {b : Nat} (hb : b + 64 ≤ ACC)
    (hb8 : b % 8 = 0) :
    WP isa (.block (VG.Proof.Curve448.AArch64.Fast.kakb b)) s fun t =>
      (∀ i < 4, word t.mem base (KA + 8 * i) = s.gpr (Mul.A i) + s.gpr (Mul.A (i + 4))) ∧
      (∀ i < 4, word t.mem base (KB + 8 * i) =
        word s.mem base (b + 8 * i) + word s.mem base (b + 32 + 8 * i)) ∧
      Outside base KA 64 s.mem t.mem ∧ Keeps [.x10, .x11, .x13] s t := by
  have hA : ACC = 3584 := rfl
  have hKA : KA = 3584 := rfl
  have hKB : KB = 3616 := rfl
  let inv := fun n (t : State) =>
    (∀ i < n, word t.mem base (KA + 8 * i) = s.gpr (Mul.A i) + s.gpr (Mul.A (i + 4))) ∧
    (∀ i < n, word t.mem base (KB + 8 * i) =
      word s.mem base (b + 8 * i) + word s.mem base (b + 32 + 8 * i)) ∧
    Outside base KA 64 s.mem t.mem ∧ Keeps [.x10, .x11, .x13] s t
  refine wp_range_flatMap (M := isa) (N := 4) inv (fun n t hn ⟨ta, tb, tO, tk⟩ => ?_) 4 (by decide) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _),
      Outside.refl _ _ _ _, Keeps.refl _ _⟩
  have ts : Scr t base := hs.of_keeps tk (by decide)
  have treg : ∀ i < 8, t.gpr (Mul.A i) = s.gpr (Mul.A i) := fun i hi => tk.1 _ (VG.Proof.Curve448.AArch64.Fast.A_ne i hi)
  have tw : ∀ d, d + 8 ≤ KA → word t.mem base d = word s.mem base d := fun d hd =>
    tO.word (Or.inl hd) (by omega)
  refine WP.mono (VG.Proof.Curve448.AArch64.Fast.kakbStep_ok ts hb hb8 hn) fun u ⟨ua, ub, uo, uk, uw⟩ => ?_
  refine ⟨fun i hi => ?_, fun i hi => ?_, tO.trans uo, tk.trans uk⟩
  · by_cases h : i = n
    · subst h; rw [ua, treg i (by omega), treg (i + 4) (by omega)]
    · rw [uw _ (by omega) (by omega) (by omega)]; exact ta i (by omega)
  · by_cases h : i = n
    · subst h; rw [ub, tw _ (by omega), tw _ (by omega)]
    · rw [uw _ (by omega) (by omega) (by omega)]; exact tb i (by omega)

theorem mul_good : VG.Proof.Curve448.AArch64.Fast.Good Mul.R [Mul.L, Mul.H, Mul.X, Mul.Y] := by decide
theorem mul_colRegs : VG.Proof.Curve448.AArch64.Fast.ColRegs Mul.R [Mul.L, Mul.H, Mul.X, Mul.Y] := by decide
theorem mul_ops : ∀ d < 4, (Mul.column d).all
    (VG.Proof.Curve448.AArch64.Fast.opOk (VG.Proof.Curve448.AArch64.Fast.writes Mul.R [Mul.L, Mul.H, Mul.X, Mul.Y]) [Mul.L, Mul.H, Mul.X, Mul.Y]) = true := by
  decide

theorem A_consts : ∀ i < 8, Mul.A i ∉ [MASK, ZERO] := by decide

theorem A_colWrites : ∀ i < 8, Mul.A i ∉ VG.Proof.Curve448.AArch64.Fast.colWrites Mul.R [Mul.L, Mul.H, Mul.X, Mul.Y] := by decide

/-- The product's limbs, from the operands' limbs. -/
abbrev prodOut (f g : Nat → Nat) : Nat → Nat := VG.Proof.Curve448.AArch64.Fast.out (VG.Proof.X448.Wide.reduced (VG.Proof.X448.Wide.rows f g 8))

theorem fits_of {f g : Nat → Nat} (hf : ∀ i < 8, f i < VG.Proof.Curve448.AArch64.Fast.Ib) (hg : ∀ i < 8, g i < VG.Proof.Curve448.AArch64.Fast.Ib) :
    VG.Proof.Curve448.AArch64.Fast.Fits (VG.Proof.X448.Wide.reduced (VG.Proof.X448.Wide.rows f g 8)) :=
  VG.Proof.Curve448.AArch64.Fast.fits fun k _ => VG.Proof.Curve448.AArch64.Fast.reduced_le (fun i hi => Nat.le_sub_one_of_lt (hf i hi))
    (fun i hi => Nat.le_sub_one_of_lt (hg i hi)) k

theorem stage_limbs {base : Addr} {o : Nat} {r : Nat → Nat} {s t : State} (hi : VG.Proof.Curve448.AArch64.Fast.ColInv base o r s t 4) :
    ∀ i < 8, (word t.mem base (o + 8 * i)).toNat =
      (if i < 4 then VG.Proof.Curve448.AArch64.Fast.chainLimb r 0 i else VG.Proof.Curve448.AArch64.Fast.chainLimb r 4 (i - 4)) := by
  intro i hi'
  by_cases h : i < 4
  · rw [ite_eq_left h]; exact hi.lo i h
  · rw [ite_eq_right h, show i = 4 + (i - 4) by omega]
    rw [hi.hi (i - 4) (by omega)]; simp

theorem finVal_out (r : Nat → Nat) :
    ∀ i < 8, VG.Proof.Curve448.AArch64.Fast.finVal (fun i => if i < 4 then VG.Proof.Curve448.AArch64.Fast.chainLimb r 0 i else VG.Proof.Curve448.AArch64.Fast.chainLimb r 4 (i - 4))
      (VG.Proof.Curve448.AArch64.Fast.chain r 0 4) (VG.Proof.Curve448.AArch64.Fast.chain r 4 4) i = VG.Proof.Curve448.AArch64.Fast.out r i := by
  intro i hi
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
      i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  all_goals simp only [VG.Proof.Curve448.AArch64.Fast.finVal, VG.Proof.Curve448.AArch64.Fast.out]; rfl

theorem mul_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat}
    (ho : o + 64 ≤ ACC) (ho8 : o % 8 = 0) (ha : a + 64 ≤ ACC) (ha8 : a % 8 = 0)
    (hb : b + 64 ≤ ACC) (hb8 : b % 8 = 0) (hob : o + 64 ≤ b ∨ b + 64 ≤ o)
    (fa : ∀ i < 8, limbs s.mem base a i < VG.Proof.Curve448.AArch64.Fast.Ib) (fb : ∀ i < 8, limbs s.mem base b i < VG.Proof.Curve448.AArch64.Fast.Ib) :
    WP isa (.block (mul o a b)) s fun t =>
      (∀ i < 8, limbs t.mem base o i = VG.Proof.Curve448.AArch64.Fast.prodOut (limbs s.mem base a) (limbs s.mem base b) i) ∧
      FieldMem base o s.mem t.mem ∧ Keeps VG.Proof.Curve448.AArch64.Fast.clob s t := by
  have hA : ACC = 3584 := rfl
  have hKA : KA = 3584 := rfl
  have hKB : KB = 3616 := rfl
  let f := limbs s.mem base a
  let g := limbs s.mem base b
  rw [VG.Proof.Curve448.AArch64.Fast.mul_split, List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.Curve448.AArch64.Fast.loadA_ok hs (by omega) ha8) fun t1 ⟨a1, m1, k1⟩ => ?_
  have s1 : Scr t1 base := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Curve448.AArch64.Fast.consts_ok t1) fun t2 ⟨mk2, z2, m2, k2⟩ => ?_
  have s2 : Scr t2 base := s1.of_keeps k2 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Curve448.AArch64.Fast.kakb_ok s2 hb hb8) fun t3 ⟨ka3, kb3, o3, k3⟩ => ?_
  have s3 : Scr t3 base := s2.of_keeps k3 (by decide)
  have A3 : ∀ i < 8, (t3.gpr (Mul.A i)).toNat = f i := by
    intro i hi
    rw [k3.1 _ (VG.Proof.Curve448.AArch64.Fast.A_ne i hi), k2.1 _ (VG.Proof.Curve448.AArch64.Fast.A_consts i hi), a1 i hi]
  have g3 : ∀ j < 8, word t3.mem base (b + 8 * j) = word s.mem base (b + 8 * j) := by
    intro j hj
    rw [o3.word (Or.inl (by omega)) (by omega), m2, m1]
  have sumlt : ∀ x y : BitVec 64, x.toNat < VG.Proof.Curve448.AArch64.Fast.Ib → y.toNat < VG.Proof.Curve448.AArch64.Fast.Ib → (x + y).toNat = x.toNat + y.toNat :=
    fun x y hx hy => by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by simp only [VG.Proof.Curve448.AArch64.Fast.Ib] at hx hy; omega)]
  have hfit := VG.Proof.Curve448.AArch64.Fast.fits_of fa fb
  let P := fun (t : State) =>
    (∀ i < 8, t.gpr (Mul.A i) = t3.gpr (Mul.A i)) ∧
    (∀ d, d + 8 ≤ 8192 → (d + 8 ≤ o ∨ o + 64 ≤ d) → word t.mem base d = word t3.mem base d)
  have hP : ∀ t u, P t → Keeps (VG.Proof.Curve448.AArch64.Fast.colWrites Mul.R [Mul.L, Mul.H, Mul.X, Mul.Y]) t u →
      Outside base o 64 t.mem u.mem → P u := by
    intro t u ⟨pa, pm⟩ k o
    exact ⟨fun i hi => (k.1 _ (VG.Proof.Curve448.AArch64.Fast.A_colWrites i hi)).trans (pa i hi),
      fun d hd hd' => (o.word hd' hd).trans (pm d hd hd')⟩
  have hsem : ∀ d < 4, ∀ t, P t → ∀ e,
      VG.Proof.Curve448.AArch64.Fast.sem (VG.Proof.Curve448.AArch64.Fast.srcVal t base b) e (Mul.column d) Mul.L = VG.Proof.X448.Wide.reduced (VG.Proof.X448.Wide.rows f g 8) d ∧
      VG.Proof.Curve448.AArch64.Fast.sem (VG.Proof.Curve448.AArch64.Fast.srcVal t base b) e (Mul.column d) Mul.H = VG.Proof.X448.Wide.reduced (VG.Proof.X448.Wide.rows f g 8) (d + 4) := by
    intro d hd t ⟨pa, pm⟩ e
    have va : ∀ i < 8, VG.Proof.Curve448.AArch64.Fast.srcVal t base b (.reg (Mul.A i)) = f i := fun i hi => by
      simp only [VG.Proof.Curve448.AArch64.Fast.srcVal]; rw [pa i hi, A3 i hi]
    have vb : ∀ j < 8, VG.Proof.Curve448.AArch64.Fast.srcVal t base b (.arg j) = g j := fun j hj => by
      simp only [VG.Proof.Curve448.AArch64.Fast.srcVal]; rw [pm _ (by omega) (by omega), g3 j hj]
    refine VG.Proof.Curve448.AArch64.Fast.mulCol_ok f g (VG.Proof.Curve448.AArch64.Fast.srcVal t base b) ?_ ?_ ?_ e hd
    · intro i j hi hj
      change ((VG.Proof.Curve448.AArch64.Fast.srcVal t base b (.reg (Mul.A i)) : Nat) : Int) * (VG.Proof.Curve448.AArch64.Fast.srcVal t base b (.arg j) : Nat) = _
      rw [va i (by omega), vb j (by omega)]
    · intro i j hi hj
      change ((VG.Proof.Curve448.AArch64.Fast.srcVal t base b (.reg (Mul.A (i + 4))) : Nat) : Int) *
        (VG.Proof.Curve448.AArch64.Fast.srcVal t base b (.arg (j + 4)) : Nat) = _
      rw [va _ (by omega), vb _ (by omega)]
    · intro i j hi hj
      change ((word t.mem base (KA + 8 * i)).toNat : Int) * ((word t.mem base (KB + 8 * j)).toNat : Int) = _
      have e1 : ∀ i < 8, (t2.gpr (Mul.A i)).toNat = f i := fun i hi => by
        rw [k2.1 _ (VG.Proof.Curve448.AArch64.Fast.A_consts i hi), a1 i hi]
      rw [pm _ (by omega) (by omega), pm _ (by omega) (by omega), ka3 i hi, kb3 j hj,
        m2, m1]
      have x1 := sumlt (t2.gpr (Mul.A i)) (t2.gpr (Mul.A (i + 4)))
        (by rw [e1 i (by omega)]; exact fa i (by omega)) (by rw [e1 (i + 4) (by omega)]; exact fa _ (by omega))
      have gb : word s.mem base (b + 32 + 8 * j) = word s.mem base (b + 8 * (j + 4)) := by
        rw [show b + 32 + 8 * j = b + 8 * (j + 4) by omega]
      have x2 := sumlt (word s.mem base (b + 8 * j)) (word s.mem base (b + 32 + 8 * j))
        (fb j (by omega)) (by rw [gb]; exact fb _ (by omega))
      rw [x1, x2, e1 i (by omega), e1 (i + 4) (by omega), gb]
      push_cast
      rfl
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Curve448.AArch64.Fast.columns_ok VG.Proof.Curve448.AArch64.Fast.mul_good VG.Proof.Curve448.AArch64.Fast.mul_colRegs (by decide) (by decide) (by decide) hb8 (by omega)
    ho8 (by omega) hfit VG.Proof.Curve448.AArch64.Fast.mul_ops P hP hsem s3 ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩
    (by rw [k3.1 _ (by decide)]; exact mk2) (by rw [k3.1 _ (by decide)]; exact z2))
    fun t4 ⟨p4, i4, k4⟩ => ?_
  have hcl := i4.cl (by decide)
  have hch := i4.ch (by decide)
  have lb : ∀ j < 8, (if j < 4 then VG.Proof.Curve448.AArch64.Fast.chainLimb (VG.Proof.X448.Wide.reduced (VG.Proof.X448.Wide.rows f g 8)) 0 j
      else VG.Proof.Curve448.AArch64.Fast.chainLimb (VG.Proof.X448.Wide.reduced (VG.Proof.X448.Wide.rows f g 8)) 4 (j - 4)) < VG.Proof.X448.Wide.radix := fun j _ => by
    split <;> exact Nat.mod_lt _ (by decide)
  refine WP.mono (VG.Proof.Curve448.AArch64.Fast.finish_ok i4.scr (by omega) ho8 i4.mask (VG.Proof.Curve448.AArch64.Fast.stage_limbs i4) lb hcl hch hfit.c₀ hfit.c₄)
    fun t5 ⟨v5, o5, k5⟩ => ⟨fun i hi => by rw [v5 i hi, VG.Proof.Curve448.AArch64.Fast.finVal_out _ i hi], ?_, ?_⟩
  · intro x h1 h2
    simp only [ofs] at h1 h2
    rw [o5 x (by simp only [ofs]; omega), i4.out x (by simp only [ofs]; omega),
      o3 x (by simp only [ofs]; omega), m2, m1]
  · refine (k1.mono ?_).trans ((k2.mono ?_).trans ((k3.mono ?_).trans ((k4.mono ?_).trans (k5.mono ?_))))
    all_goals intro r hr; revert r; decide

end VG.Proof.Curve448.AArch64.Fast

end

/- Proofs formerly in `VerifiedGarbage.Proof.Curve448.AArch64.Fast.Sqr`. -/
section

/-!
# Squaring

Untrusted: everything here is checked by Lean. `sqr o a` writes the same
limbs as `mul o a a`, from 30 products.
-/

namespace VG.Proof.Curve448.AArch64.Fast

open VG VG.AArch64
open VG.Impl.Curve448.AArch64.Fast
open VG.Impl.X448.AArch64 (ld st ACC)
open VG.Proof.X448.Wide (radix pair rows reduced)
open VG.Proof.X448.AArch64 (Keeps Scr word off Outside writeW_outside limbs FieldMem ofs)

def zadds : List Instr := (List.range 4).map fun i => .add .x (Sqr.Z i) (Sqr.A i) (Sqr.A (i + 4))

def doubles : List Instr :=
  (List.range 3).flatMap (fun k => (List.range 3).flatMap fun h =>
    [.add .x Sqr.R.t (Sqr.limb h k) (Sqr.limb h k), st Sqr.R.t (KD + 24 * h + 8 * k)])

theorem sqr_split (o a : Nat) :
    sqr o a = loadA a ++ consts ++ VG.Proof.Curve448.AArch64.Fast.zadds ++ VG.Proof.Curve448.AArch64.Fast.doubles ++ columns Sqr.R a Sqr.L Sqr.H Sqr.column o ++
      finish o := rfl

def zRegs : List Reg := [.x10, .x11, .x13, .x14]

theorem Z_facts : ∀ i < 4, Sqr.Z i ∈ VG.Proof.Curve448.AArch64.Fast.zRegs ∧ ∀ j < 8, Sqr.A j ≠ Sqr.Z i := by decide
theorem Z_inj : ∀ i < 4, ∀ j < 4, i ≠ j → Sqr.Z i ≠ Sqr.Z j := by decide

theorem zadds_ok (s : State) :
    WP isa (.block VG.Proof.Curve448.AArch64.Fast.zadds) s fun t =>
      (∀ i < 4, t.gpr (Sqr.Z i) = s.gpr (Sqr.A i) + s.gpr (Sqr.A (i + 4))) ∧ t.mem = s.mem ∧
      Keeps VG.Proof.Curve448.AArch64.Fast.zRegs s t := by
  have e : VG.Proof.Curve448.AArch64.Fast.zadds = (List.range 4).flatMap fun i => [.add .x (Sqr.Z i) (Sqr.A i) (Sqr.A (i + 4))] := by
    simp only [VG.Proof.Curve448.AArch64.Fast.zadds]; rfl
  rw [e]
  let inv := fun n (t : State) =>
    (∀ i < n, t.gpr (Sqr.Z i) = s.gpr (Sqr.A i) + s.gpr (Sqr.A (i + 4))) ∧ t.mem = s.mem ∧
    Keeps VG.Proof.Curve448.AArch64.Fast.zRegs s t
  refine wp_range_flatMap (M := isa) (N := 4) inv (fun n t hn ⟨tv, tm, tk⟩ => ?_) 4 (by decide) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), rfl, Keeps.refl _ _⟩
  refine WP.mono (VG.Proof.Curve448.AArch64.Fast.add_ok t _ _ _) fun u ⟨uv, um, uk⟩ => ?_
  have aA : ∀ j < 8, t.gpr (Sqr.A j) = s.gpr (Sqr.A j) := fun j hj => tk.1 _ (by
    intro h
    simp only [VG.Proof.Curve448.AArch64.Fast.zRegs, List.mem_cons, List.not_mem_nil, or_false] at h
    revert h; revert j; decide)
  refine ⟨fun i hi => ?_, um.trans tm, tk.trans (uk.mono fun r hr => ?_)⟩
  · by_cases h : i = n
    · subst h; rw [uv, aA i (by omega), aA (i + 4) (by omega)]
    · have hne : Sqr.Z i ∉ [Sqr.Z n] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        exact VG.Proof.Curve448.AArch64.Fast.Z_inj i (by omega) n hn h
      rw [uk.1 _ hne, tv i (by omega)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [hr]; exact (VG.Proof.Curve448.AArch64.Fast.Z_facts n hn).1

theorem limb_ne : ∀ h < 3, ∀ k < 3, Sqr.limb h k ≠ Sqr.R.t ∧ Sqr.limb h k ≠ .x3 := by decide

/-- One doubled limb. -/
theorem double_ok {s : State} {base : Addr} (hs : Scr s base) {h k : Nat} (hh : h < 3) (hk : k < 3) :
    WP isa (.block [.add .x Sqr.R.t (Sqr.limb h k) (Sqr.limb h k), st Sqr.R.t (KD + 24 * h + 8 * k)]) s
      fun t => (∀ d, d + 8 ≤ 8192 → (d = KD + 24 * h + 8 * k ∨ d + 8 ≤ KD + 24 * h + 8 * k ∨
          KD + 24 * h + 8 * k + 8 ≤ d) →
        word t.mem base d = if d = KD + 24 * h + 8 * k then
          s.gpr (Sqr.limb h k) + s.gpr (Sqr.limb h k) else word s.mem base d) ∧
        Keeps [Sqr.R.t] s t ∧ Outside base KD 72 s.mem t.mem := by
  have hKD : KD = 3648 := rfl
  rw [show [Instr.add .x Sqr.R.t (Sqr.limb h k) (Sqr.limb h k), st Sqr.R.t (KD + 24 * h + 8 * k)] =
    [Instr.add .x Sqr.R.t (Sqr.limb h k) (Sqr.limb h k)] ++ [st Sqr.R.t (KD + 24 * h + 8 * k)] from rfl,
    WP.block_append_iff]
  refine WP.mono (VG.Proof.Curve448.AArch64.Fast.add_ok s _ _ _) fun u ⟨uv, um, uk⟩ => ?_
  have us : Scr u base := hs.of_keeps uk (by decide)
  refine WP.mono (VG.Proof.Curve448.AArch64.Fast.stw_ok us _ (d := KD + 24 * h + 8 * k) (by omega) (by omega))
    fun t ⟨tw, tO, tg, tr, twr⟩ => ⟨fun d hd hs' => ?_, ?_, by rw [← um]; exact tO.mono (by omega) (by omega)⟩
  · rw [tw d hd hs', uv, um]
  · refine ⟨fun q hq => ?_, tr.trans uk.2.1, twr.trans uk.2.2⟩
    rw [tg, uk.1 q hq]

theorem doubles_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block VG.Proof.Curve448.AArch64.Fast.doubles) s fun t =>
      (∀ h < 3, ∀ k < 3, word t.mem base (KD + 24 * h + 8 * k) =
        s.gpr (Sqr.limb h k) + s.gpr (Sqr.limb h k)) ∧
      (∀ d, d + 8 ≤ 8192 → (d + 8 ≤ KD ∨ KD + 72 ≤ d) → word t.mem base d = word s.mem base d) ∧
      Keeps [Sqr.R.t] s t ∧ Outside base KD 72 s.mem t.mem := by
  have hKD : KD = 3648 := rfl
  have reg : ∀ (t : State), Keeps [Sqr.R.t] s t → ∀ h < 3, ∀ k < 3,
      t.gpr (Sqr.limb h k) = s.gpr (Sqr.limb h k) := fun t tk h hh k hk =>
    tk.1 _ (by simp only [List.mem_cons, List.not_mem_nil, or_false]; exact (VG.Proof.Curve448.AArch64.Fast.limb_ne h hh k hk).1)
  let inv := fun n (t : State) =>
    (∀ k < n, ∀ h < 3, word t.mem base (KD + 24 * h + 8 * k) =
      s.gpr (Sqr.limb h k) + s.gpr (Sqr.limb h k)) ∧
    (∀ d, d + 8 ≤ 8192 → (d + 8 ≤ KD ∨ KD + 24 * 3 ≤ d ∨
        (∃ h < 3, ∃ k < 3, n ≤ k ∧ d = KD + 24 * h + 8 * k)) → word t.mem base d = word s.mem base d) ∧
    Keeps [Sqr.R.t] s t ∧ Outside base KD 72 s.mem t.mem
  have outer := wp_range_flatMap (M := isa) (N := 3)
    (f := fun k => (List.range 3).flatMap fun h =>
      [.add .x Sqr.R.t (Sqr.limb h k) (Sqr.limb h k), st Sqr.R.t (KD + 24 * h + 8 * k)]) inv ?_ 3
    (by decide) s ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ => rfl, Keeps.refl _ _,
      Outside.refl _ _ _ _⟩
  · refine WP.mono outer fun t ⟨tv, tm, tk, tO⟩ => ⟨fun h hh k hk => tv k hk h hh,
      fun d hd hd' => tm d hd (by omega), tk, tO⟩
  · intro n t hn ⟨tv, tm, tk, tO⟩
    let ininv := fun m (u : State) =>
      (∀ k < n, ∀ h < 3, word u.mem base (KD + 24 * h + 8 * k) =
        s.gpr (Sqr.limb h k) + s.gpr (Sqr.limb h k)) ∧
      (∀ h < m, word u.mem base (KD + 24 * h + 8 * n) = s.gpr (Sqr.limb h n) + s.gpr (Sqr.limb h n)) ∧
      (∀ d, d + 8 ≤ 8192 → (d + 8 ≤ KD ∨ KD + 24 * 3 ≤ d ∨
          (∃ h < 3, ∃ k < 3, n + 1 ≤ k ∧ d = KD + 24 * h + 8 * k) ∨
          (∃ h < 3, m ≤ h ∧ d = KD + 24 * h + 8 * n)) → word u.mem base d = word s.mem base d) ∧
      Keeps [Sqr.R.t] s u ∧ Outside base KD 72 s.mem u.mem
    have c0 : ∀ d, (d + 8 ≤ KD ∨ KD + 24 * 3 ≤ d ∨
        (∃ h < 3, ∃ k < 3, n + 1 ≤ k ∧ d = KD + 24 * h + 8 * k) ∨
        (∃ h < 3, 0 ≤ h ∧ d = KD + 24 * h + 8 * n)) →
        (d + 8 ≤ KD ∨ KD + 24 * 3 ≤ d ∨ (∃ h < 3, ∃ k < 3, n ≤ k ∧ d = KD + 24 * h + 8 * k)) := by
      intro d hd'
      rcases hd' with h | h | ⟨h, hh, k, hk, hnk, e⟩ | ⟨h, hh, _, e⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨h, hh, k, hk, by omega, e⟩)
      · exact Or.inr (Or.inr ⟨h, hh, n, hn, Nat.le_refl _, e⟩)
    have c3 : ∀ d, (d + 8 ≤ KD ∨ KD + 24 * 3 ≤ d ∨
        (∃ h < 3, ∃ k < 3, n + 1 ≤ k ∧ d = KD + 24 * h + 8 * k)) →
        (d + 8 ≤ KD ∨ KD + 24 * 3 ≤ d ∨
          (∃ h < 3, ∃ k < 3, n + 1 ≤ k ∧ d = KD + 24 * h + 8 * k) ∨
          (∃ h < 3, 3 ≤ h ∧ d = KD + 24 * h + 8 * n)) := by
      intro d hd'
      rcases hd' with h | h | ⟨h, hh, k, hk, hnk, e⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl ⟨h, hh, k, hk, hnk, e⟩))
    refine WP.mono (wp_range_flatMap (M := isa) (N := 3) ininv (fun m u hm ⟨uv, uw, um, uk, uO⟩ => ?_) 3
      (by decide) t ⟨tv, fun _ h => absurd h (Nat.not_lt_zero _), fun d hd hd' => tm d hd (c0 d hd'), tk, tO⟩)
      fun u ⟨uv, uw, um, uk, uO⟩ => ⟨fun k hk h hh => ?_, fun d hd hd' => um d hd (c3 d hd'), uk, uO⟩
    · have us : Scr u base := hs.of_keeps uk (by decide)
      refine WP.mono (VG.Proof.Curve448.AArch64.Fast.double_ok us hm hn) fun w ⟨ww, wk, wO⟩ => ⟨fun k hk h hh => ?_, fun h hh => ?_,
        fun d hd hd' => ?_, uk.trans wk, uO.trans wO⟩
      · rw [ww _ (by omega) (by omega), ite_eq_right (by omega)]; exact uv k hk h hh
      · rw [ww _ (by omega) (by omega)]
        by_cases e : h = m
        · subst e; rw [ite_eq_left rfl, reg u uk h hm n hn]
        · rw [ite_eq_right (by omega)]; exact uw h (by omega)
      · have hne : d ≠ KD + 24 * m + 8 * n ∧ (d + 8 ≤ KD + 24 * m + 8 * n ∨
            KD + 24 * m + 8 * n + 8 ≤ d) := by
          rcases hd' with h | h | ⟨h, hh, k, hk, hnk, e⟩ | ⟨h, hh, hmh, e⟩ <;> omega
        have hd2 : d + 8 ≤ KD ∨ KD + 24 * 3 ≤ d ∨
            (∃ h < 3, ∃ k < 3, n + 1 ≤ k ∧ d = KD + 24 * h + 8 * k) ∨
            (∃ h < 3, m ≤ h ∧ d = KD + 24 * h + 8 * n) := by
          rcases hd' with h | h | ⟨h, hh, k, hk, hnk, e⟩ | ⟨h, hh, hmh, e⟩
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Or.inl ⟨h, hh, k, hk, hnk, e⟩))
          · exact Or.inr (Or.inr (Or.inr ⟨h, hh, by omega, e⟩))
        rw [ww d hd (Or.inr hne.2), ite_eq_right hne.1]
        exact um d hd hd2
    · by_cases e : k = n
      · subst e; exact uw h hh
      · exact uv k (by omega) h hh

theorem sqr_good : VG.Proof.Curve448.AArch64.Fast.Good Sqr.R [Sqr.L, Sqr.H] := by decide
theorem sqr_colRegs : VG.Proof.Curve448.AArch64.Fast.ColRegs Sqr.R [Sqr.L, Sqr.H] := by decide
theorem sqr_ops : ∀ d < 4, (Sqr.column d).all
    (VG.Proof.Curve448.AArch64.Fast.opOk (VG.Proof.Curve448.AArch64.Fast.writes Sqr.R [Sqr.L, Sqr.H]) [Sqr.L, Sqr.H]) = true := by decide
theorem AZ_colWrites : ∀ h < 3, ∀ i < 4, Sqr.limb h i ∉ VG.Proof.Curve448.AArch64.Fast.colWrites Sqr.R [Sqr.L, Sqr.H] := by decide
theorem AZ_pre : ∀ h < 3, ∀ i < 4, Sqr.limb h i ∉ [Sqr.R.t] := by decide
theorem A_z : ∀ i < 8, Mul.A i ∉ VG.Proof.Curve448.AArch64.Fast.zRegs := by decide

/-- The value of limb `i` of half `h`. -/
def lv (f : Nat → Nat) (h i : Nat) : Nat := match h with
  | 0 => f i
  | 1 => f (i + 4)
  | _ => f i + f (i + 4)

theorem sqr_ok {s : State} {base : Addr} (hs : Scr s base) {o a : Nat}
    (ho : o + 64 ≤ ACC) (ho8 : o % 8 = 0) (ha : a + 64 ≤ ACC) (ha8 : a % 8 = 0)
    (fa : ∀ i < 8, limbs s.mem base a i < VG.Proof.Curve448.AArch64.Fast.Ib) :
    WP isa (.block (sqr o a)) s fun t =>
      (∀ i < 8, limbs t.mem base o i = VG.Proof.Curve448.AArch64.Fast.prodOut (limbs s.mem base a) (limbs s.mem base a) i) ∧
      FieldMem base o s.mem t.mem ∧ Keeps VG.Proof.Curve448.AArch64.Fast.clob s t := by
  have hA : ACC = 3584 := rfl
  have hKD : KD = 3648 := rfl
  let f := limbs s.mem base a
  rw [VG.Proof.Curve448.AArch64.Fast.sqr_split, List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc,
    WP.block_append_iff]
  refine WP.mono (VG.Proof.Curve448.AArch64.Fast.loadA_ok hs (by omega) ha8) fun t1 ⟨a1, m1, k1⟩ => ?_
  have s1 : Scr t1 base := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Curve448.AArch64.Fast.consts_ok t1) fun t2 ⟨mk2, z2, m2, k2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Curve448.AArch64.Fast.zadds_ok t2) fun t3 ⟨z3, m3, k3⟩ => ?_
  have s3 : Scr t3 base := (s1.of_keeps k2 (by decide)).of_keeps k3 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Curve448.AArch64.Fast.doubles_ok s3) fun t4 ⟨d4, o4, k4, O4⟩ => ?_
  have s4 : Scr t4 base := s3.of_keeps k4 (by decide)
  have sumlt : ∀ x y : BitVec 64, x.toNat < 2 ^ 63 → y.toNat < 2 ^ 63 →
      (x + y).toNat = x.toNat + y.toNat := fun x y hx hy => by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have fI : ∀ i < 8, f i < VG.Proof.Curve448.AArch64.Fast.Ib := fa
  have A2 : ∀ i < 8, (t2.gpr (Mul.A i)).toNat = f i := fun i hi => by
    rw [k2.1 _ (VG.Proof.Curve448.AArch64.Fast.A_consts i hi), a1 i hi]
  have L4 : ∀ h < 3, ∀ i < 4, (t4.gpr (Sqr.limb h i)).toNat = VG.Proof.Curve448.AArch64.Fast.lv f h i := by
    intro h hh i hi
    rw [k4.1 _ (VG.Proof.Curve448.AArch64.Fast.AZ_pre h hh i hi)]
    obtain rfl | rfl | rfl : h = 0 ∨ h = 1 ∨ h = 2 := by omega
    · change (t3.gpr (Mul.A i)).toNat = _
      rw [k3.1 _ (VG.Proof.Curve448.AArch64.Fast.A_z i (by omega)), A2 i (by omega)]; rfl
    · change (t3.gpr (Mul.A (i + 4))).toNat = _
      rw [k3.1 _ (VG.Proof.Curve448.AArch64.Fast.A_z (i + 4) (by omega)), A2 (i + 4) (by omega)]; rfl
    · change (t3.gpr (Sqr.Z i)).toNat = _
      rw [z3 i hi]
      change (t2.gpr (Mul.A i) + t2.gpr (Mul.A (i + 4))).toNat = _
      rw [sumlt _ _ (by rw [A2 i (by omega)]; have := fI i (by omega); simp only [VG.Proof.Curve448.AArch64.Fast.Ib] at this; omega)
        (by rw [A2 _ (by omega)]; have := fI (i + 4) (by omega); simp only [VG.Proof.Curve448.AArch64.Fast.Ib] at this; omega)]
      rw [A2 i (by omega), A2 _ (by omega)]; rfl
  have lvb : ∀ h < 3, ∀ i < 4, VG.Proof.Curve448.AArch64.Fast.lv f h i < 2 ^ 62 := by
    intro h hh i hi
    have := fI i (by omega); have := fI (i + 4) (by omega)
    obtain rfl | rfl | rfl : h = 0 ∨ h = 1 ∨ h = 2 := by omega
    all_goals simp only [VG.Proof.Curve448.AArch64.Fast.lv, VG.Proof.Curve448.AArch64.Fast.Ib] at *; omega
  have D4 : ∀ h < 3, ∀ k < 3, (word t4.mem base (KD + 24 * h + 8 * k)).toNat = 2 * VG.Proof.Curve448.AArch64.Fast.lv f h k := by
    intro h hh k hk
    rw [d4 h hh k hk]
    have e : t3.gpr (Sqr.limb h k) = t4.gpr (Sqr.limb h k) := (k4.1 _ (VG.Proof.Curve448.AArch64.Fast.AZ_pre h hh k (by omega))).symm
    rw [e, sumlt _ _ (by rw [L4 h hh k (by omega)]; have := lvb h hh k (by omega); omega)
      (by rw [L4 h hh k (by omega)]; have := lvb h hh k (by omega); omega), L4 h hh k (by omega)]
    omega
  have hfit := VG.Proof.Curve448.AArch64.Fast.fits_of fa fa
  let P := fun (t : State) =>
    (∀ h < 3, ∀ i < 4, t.gpr (Sqr.limb h i) = t4.gpr (Sqr.limb h i)) ∧
    (∀ d, d + 8 ≤ 8192 → (d + 8 ≤ o ∨ o + 64 ≤ d) → word t.mem base d = word t4.mem base d)
  have hP : ∀ t u, P t → Keeps (VG.Proof.Curve448.AArch64.Fast.colWrites Sqr.R [Sqr.L, Sqr.H]) t u →
      Outside base o 64 t.mem u.mem → P u := by
    intro t u ⟨pa, pm⟩ k o
    exact ⟨fun h hh i hi => (k.1 _ (VG.Proof.Curve448.AArch64.Fast.AZ_colWrites h hh i hi)).trans (pa h hh i hi),
      fun d hd hd' => (o.word hd' hd).trans (pm d hd hd')⟩
  have hsem : ∀ d < 4, ∀ t, P t → ∀ e,
      VG.Proof.Curve448.AArch64.Fast.sem (VG.Proof.Curve448.AArch64.Fast.srcVal t base a) e (Sqr.column d) Sqr.L = VG.Proof.X448.Wide.reduced (VG.Proof.X448.Wide.rows f f 8) d ∧
      VG.Proof.Curve448.AArch64.Fast.sem (VG.Proof.Curve448.AArch64.Fast.srcVal t base a) e (Sqr.column d) Sqr.H = VG.Proof.X448.Wide.reduced (VG.Proof.X448.Wide.rows f f 8) (d + 4) := by
    intro d hd t ⟨pa, pm⟩ e
    have hv : ∀ h < 3, ∀ i j, i ≤ j → j < 4 →
        ((VG.Proof.Curve448.AArch64.Fast.srcVal t base a (Sqr.src h (i, j)).1 : Nat) : Int) * (VG.Proof.Curve448.AArch64.Fast.srcVal t base a (Sqr.src h (i, j)).2 : Nat) =
        (if i = j then 1 else 2) * (VG.Proof.Curve448.AArch64.Fast.lv f h i : Int) * VG.Proof.Curve448.AArch64.Fast.lv f h j := by
      intro h hh i j hij hj
      by_cases e : i = j
      · subst e
        simp only [Sqr.src, ite_true, VG.Proof.Curve448.AArch64.Fast.srcVal, pa h hh i hj, L4 h hh i hj]
        grind
      · simp only [Sqr.src, e, ite_false, VG.Proof.Curve448.AArch64.Fast.srcVal, pa h hh j hj, L4 h hh j hj]
        rw [pm _ (by omega) (by omega), D4 h hh i (by omega)]
        grind
    refine VG.Proof.Curve448.AArch64.Fast.sqrCol_ok f (VG.Proof.Curve448.AArch64.Fast.srcVal t base a) ?_ ?_ ?_ e hd
    · intro i j hij hj; rw [hv 0 (by decide) i j hij hj]; rfl
    · intro i j hij hj; rw [hv 1 (by decide) i j hij hj]; rfl
    · intro i j hij hj; rw [hv 2 (by decide) i j hij hj]; simp only [VG.Proof.Curve448.AArch64.Fast.lv]; grind
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Curve448.AArch64.Fast.columns_ok VG.Proof.Curve448.AArch64.Fast.sqr_good VG.Proof.Curve448.AArch64.Fast.sqr_colRegs (by decide) (by decide) (by decide) ha8 (by omega)
    ho8 (by omega)
    hfit VG.Proof.Curve448.AArch64.Fast.sqr_ops P hP hsem s4 ⟨fun _ _ _ _ => rfl, fun _ _ _ => rfl⟩
    (by rw [k4.1 _ (by decide), k3.1 _ (by decide)]; exact mk2)
    (by rw [k4.1 _ (by decide), k3.1 _ (by decide)]; exact z2))
    fun t5 ⟨p5, i5, k5⟩ => ?_
  have lb : ∀ j < 8, (if j < 4 then VG.Proof.Curve448.AArch64.Fast.chainLimb (VG.Proof.X448.Wide.reduced (VG.Proof.X448.Wide.rows f f 8)) 0 j
      else VG.Proof.Curve448.AArch64.Fast.chainLimb (VG.Proof.X448.Wide.reduced (VG.Proof.X448.Wide.rows f f 8)) 4 (j - 4)) < VG.Proof.X448.Wide.radix := fun j _ => by
    split <;> exact Nat.mod_lt _ (by decide)
  refine WP.mono (VG.Proof.Curve448.AArch64.Fast.finish_ok i5.scr (by omega) ho8 i5.mask (VG.Proof.Curve448.AArch64.Fast.stage_limbs i5) lb (i5.cl (by decide))
    (i5.ch (by decide)) hfit.c₀ hfit.c₄)
    fun t6 ⟨v6, o6, k6⟩ => ⟨fun i hi => by rw [v6 i hi, VG.Proof.Curve448.AArch64.Fast.finVal_out _ i hi], ?_, ?_⟩
  · intro x h1 h2
    simp only [ofs] at h1 h2
    have e4 : t4.mem x = t3.mem x := O4 x (by simp only [ofs]; omega)
    rw [o6 x (by simp only [ofs]; omega), i5.out x (by simp only [ofs]; omega), e4, m3, m2, m1]
  · refine (k1.mono ?_).trans ((k2.mono ?_).trans ((k3.mono ?_).trans ((k4.mono ?_).trans
      ((k5.mono ?_).trans (k6.mono ?_)))))
    all_goals intro r hr; revert r; decide

end VG.Proof.Curve448.AArch64.Fast

end

/- Proofs formerly in `VerifiedGarbage.Proof.Curve448.AArch64.Fast.Limbwise`. -/
section

/-!
# Limb-by-limb operations

Untrusted: everything here is checked by Lean. `limbs_loop`: eight steps,
step `i` writing limb `i` of each output slot from the unchanged inputs.
-/

namespace VG.Proof.Curve448.AArch64.Fast

open VG VG.AArch64
open VG.Impl.Curve448.AArch64.Fast
open VG.Impl.X448.AArch64 (ld st ACC)
open VG.Proof.X448.Wide (radix)
open VG.Proof.X448.AArch64 (Keeps Scr word off Outside writeW_outside limbs FieldMem ofs)

/-- Byte `x` is outside every output slot (64 bytes from each of `outs`). -/
def Away (base : Addr) (outs : List Nat) (n : Nat) (x : Addr) : Prop :=
  ∀ o ∈ outs, ofs base x < o ∨ o + n ≤ ofs base x

theorem word_congr {base : Addr} {m m' : Mem} {d : Nat} (hd : d + 8 ≤ 8192)
    (h : ∀ x, d ≤ ofs base x → ofs base x < d + 8 → m' x = m x) : word m' base d = word m base d :=
  (Mem.readW_congr fun i hi => (h _ (by rw [VG.Proof.X448.AArch64.ofs_off base (by omega)]; omega)
    (by rw [VG.Proof.X448.AArch64.ofs_off base (by omega)]; omega)).symm).symm

theorem limbs_loop {base : Addr} {body : Nat → List Instr} {outs : List Nat} {rs : List Reg}
    (P : State → Prop) (hP : ∀ t u, P t → Keeps rs t u → P u) (hrs : .x3 ∉ rs ∧ .x12 ∉ rs)
    (V : Nat → Nat → BitVec 64) (s : State)
    (hstep : ∀ i < 8, ∀ t, Scr t base → P t → (∀ x, VG.Proof.Curve448.AArch64.Fast.Away base outs 64 x → t.mem x = s.mem x) →
      WP isa (.block (body i)) t fun u =>
        (∀ o ∈ outs, word u.mem base (o + 8 * i) = V o i) ∧
        (∀ x, (∀ o ∈ outs, ofs base x < o + 8 * i ∨ o + 8 * i + 8 ≤ ofs base x) → u.mem x = t.mem x) ∧
        Keeps rs t u)
    (hw : ∀ o ∈ outs, o + 64 ≤ 8192) (sep : ∀ o ∈ outs, ∀ o' ∈ outs, o ≠ o' → o + 64 ≤ o' ∨ o' + 64 ≤ o)
    (hs : Scr s base) (hP0 : P s) :
    WP isa (.block ((List.range 8).flatMap body)) s fun t =>
      (∀ o ∈ outs, ∀ i < 8, word t.mem base (o + 8 * i) = V o i) ∧
      (∀ x, VG.Proof.Curve448.AArch64.Fast.Away base outs 64 x → t.mem x = s.mem x) ∧ Keeps rs s t := by
  let inv := fun n (t : State) =>
    Scr t base ∧ P t ∧ (∀ o ∈ outs, ∀ i < n, word t.mem base (o + 8 * i) = V o i) ∧
      (∀ x, (∀ o ∈ outs, ofs base x < o ∨ o + 8 * n ≤ ofs base x) → t.mem x = s.mem x) ∧
      Keeps rs s t
  refine WP.mono (wp_range_flatMap (M := isa) (N := 8) inv (fun n t hn ⟨ts, tp, tv, tm, tk⟩ => ?_) 8
    (by decide) s ⟨hs, hP0, fun _ _ _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl, Keeps.refl _ _⟩)
    fun t ⟨_, _, tv, tm, tk⟩ => ⟨tv, fun x hx => tm x hx, tk⟩
  refine WP.mono (hstep n hn t ts tp (fun x hx => tm x fun o ho => by
    have := hx o ho; omega)) fun u ⟨uv, um, uk⟩ => ⟨ts.of_keeps uk hrs, hP t u tp uk, ?_, ?_, tk.trans uk⟩
  · intro o ho i hi
    by_cases h : i = n
    · subst h; exact uv o ho
    · rw [← tv o ho i (by omega)]
      have ho64 := hw o ho
      refine VG.Proof.Curve448.AArch64.Fast.word_congr (by omega) fun x h1 h2 => um x fun o' ho' => ?_
      by_cases e : o' = o
      · subst e; omega
      · have := sep o ho o' ho' (Ne.symm e)
        omega
  · intro x hx
    rw [um x (fun o ho => by have := hx o ho; omega), tm x (fun o ho => by have := hx o ho; omega)]

end VG.Proof.Curve448.AArch64.Fast

end

/- Proofs formerly in `VerifiedGarbage.Proof.Curve448.AArch64.Fast.Sub`. -/
section

/-!
# Differences and sums

Untrusted: everything here is checked by Lean. `sub o a b` writes
`a + 2p - b` limb by limb, and `addSub` also `a + b`.
-/

namespace VG.Proof.Curve448.AArch64.Fast

open VG VG.AArch64
open VG.Impl.Curve448.AArch64.Fast
open VG.Impl.X448.AArch64 (ld st ACC)
open VG.Proof.X448.Wide (radix)
open VG.Proof.X448.AArch64 (Keeps Scr word off Outside writeW_outside limbs FieldMem ofs read8_eq
  write8_eq)
open VG.Proof.Ed25519.AArch64 (read_x)

def K2 : BitVec 64 := BitVec.ofNat 64 (2 ^ 57 - 2)
def K4 : BitVec 64 := BitVec.ofNat 64 (2 ^ 57 - 4)

def twoPW (i : Nat) : BitVec 64 := if i = 4 then VG.Proof.Curve448.AArch64.Fast.K4 else VG.Proof.Curve448.AArch64.Fast.K2

theorem twoPRegs_ok (s : State) :
    WP isa (.block twoPRegs) s fun t =>
      t.gpr .x0 = VG.Proof.Curve448.AArch64.Fast.K2 ∧ t.gpr .x2 = VG.Proof.Curve448.AArch64.Fast.K4 ∧ t.mem = s.mem ∧ Keeps [.x0, .x2] s t := by
  refine WP.of_runBlock ⟨_, by
    simp only [twoPRegs, runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
      show 16 * 0 < 64 from by decide, show 16 * 1 < 64 from by decide,
      show 16 * 2 < 64 from by decide, show 16 * 3 < 64 from by decide, ite_true]; rfl, ?_⟩
  refine ⟨?_, ?_, rfl, fun q hq => ?_, rfl, rfl⟩
  · simp only [State.read, RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false]
    decide
  · simp only [State.read, RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false]
    decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp only [RegUpd.gpr_write, hq.1, hq.2, ite_false]

theorem twoPReg_val {t : State} (h0 : t.gpr .x0 = VG.Proof.Curve448.AArch64.Fast.K2) (h2 : t.gpr .x2 = VG.Proof.Curve448.AArch64.Fast.K4) (i : Nat) :
    t.gpr (twoPReg i) = VG.Proof.Curve448.AArch64.Fast.twoPW i := by
  simp only [twoPReg, VG.Proof.Curve448.AArch64.Fast.twoPW]; split <;> with_reducible assumption

/-- Load two words, from the working space. -/
theorem ld2 {t : State} {base : Addr} (ht : Scr t base) {d e : Nat} (hd : d % 8 = 0) (hd' : d + 8 ≤ 8192)
    (he : e % 8 = 0) (he' : e + 8 ≤ 8192) :
    InRegions (t.rd ++ t.wr) (base + BitVec.ofNat 64 d) 8 ∧
      (d % 8 = 0 ∧ d < 4096 * 8) ∧ InRegions (t.rd ++ t.wr) (base + BitVec.ofNat 64 e) 8 ∧
      (e % 8 = 0 ∧ e < 4096 * 8) :=
  ⟨ht.read hd', ⟨hd, by omega⟩, ht.read he', ⟨he, by omega⟩⟩

theorem subStep_ok {t : State} {base : Addr} (ht : Scr t base) {o a b i : Nat} (hi : i < 8)
    (ho : o + 64 ≤ 8192) (ha : a + 64 ≤ 8192) (hb : b + 64 ≤ 8192) (ho8 : o % 8 = 0) (ha8 : a % 8 = 0)
    (hb8 : b % 8 = 0) (h0 : t.gpr .x0 = VG.Proof.Curve448.AArch64.Fast.K2) (h2 : t.gpr .x2 = VG.Proof.Curve448.AArch64.Fast.K4) :
    WP isa (.block [ld .x4 (a + 8 * i), ld .x5 (b + 8 * i), .add .x .x4 .x4 (twoPReg i),
      .sub .x .x4 .x4 .x5, st .x4 (o + 8 * i)]) t fun u =>
      u.mem = t.mem.writeW (off base (o + 8 * i))
        (word t.mem base (a + 8 * i) + VG.Proof.Curve448.AArch64.Fast.twoPW i - word t.mem base (b + 8 * i)) ∧
      Keeps [.x4, .x5] t u := by
  obtain ⟨ra, aa, rb, ab⟩ := VG.Proof.Curve448.AArch64.Fast.ld2 ht (d := a + 8 * i) (e := b + 8 * i) (by omega) (by omega) (by omega)
    (by omega)
  have wo := ht.write (d := o + 8 * i) (n := 8) (by omega)
  have ao : (o + 8 * i) % 8 = 0 ∧ o + 8 * i < 4096 * 8 := ⟨by omega, by omega⟩
  have tw : twoPReg i ≠ .x4 ∧ twoPReg i ≠ .x5 := by simp only [twoPReg]; split <;> decide
  refine WP.of_runBlock ⟨_, by
    simp only [ld, st, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
      State.load, State.store, read_x, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write,
      RegUpd.wr_write, reduceCtorEq, ite_true, ite_false, ht.x3, aa, ab, ao, ra, rb, wo, and_self,
      Option.map_some, Option.bind_some]; rfl, ?_⟩
  refine ⟨?_, fun q hq => ?_, rfl, rfl⟩
  · simp only [tw.1, tw.2, ite_false, BitVec.setWidth_eq, write8_eq, read8_eq, VG.Proof.Curve448.AArch64.Fast.twoPReg_val h0 h2]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp only [RegUpd.gpr_write, hq.1, hq.2, ite_false]

theorem away_word {base : Addr} {outs : List Nat} {m m' : Mem}
    (h : ∀ x, VG.Proof.Curve448.AArch64.Fast.Away base outs 64 x → m' x = m x) {d : Nat} (hd : d + 8 ≤ 8192)
    (ho : ∀ o ∈ outs, d + 8 ≤ o ∨ o + 64 ≤ d) : word m' base d = word m base d :=
  VG.Proof.Curve448.AArch64.Fast.word_congr hd fun x h1 h2 => h x fun o h' => by have := ho o h'; omega

theorem writeW_frame {base : Addr} (m : Mem) {d : Nat} (hd : d + 8 ≤ 8192) (v : BitVec 64) (x : Addr)
    (hx : ofs base x < d ∨ d + 8 ≤ ofs base x) : (m.writeW (off base d) v) x = m x :=
  writeW_outside m base v hd x hx

theorem sub_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat}
    (ho : o + 64 ≤ 8192) (ha : a + 64 ≤ 8192) (hb : b + 64 ≤ 8192) (ho8 : o % 8 = 0) (ha8 : a % 8 = 0)
    (hb8 : b % 8 = 0) (hoa : o + 64 ≤ a ∨ a + 64 ≤ o) (hob : o + 64 ≤ b ∨ b + 64 ≤ o) :
    WP isa (.block (Impl.Curve448.AArch64.Fast.sub o a b)) s fun t =>
      (∀ i < 8, word t.mem base (o + 8 * i) =
        word s.mem base (a + 8 * i) + VG.Proof.Curve448.AArch64.Fast.twoPW i - word s.mem base (b + 8 * i)) ∧
      (∀ x, VG.Proof.Curve448.AArch64.Fast.Away base [o] 64 x → t.mem x = s.mem x) ∧ Keeps [.x0, .x2, .x4, .x5] s t := by
  rw [Impl.Curve448.AArch64.Fast.sub, WP.block_append_iff]
  refine WP.mono (VG.Proof.Curve448.AArch64.Fast.twoPRegs_ok s) fun t ⟨t0, t2, tm, tk⟩ => ?_
  have ts : Scr t base := hs.of_keeps tk (by decide)
  have := VG.Proof.Curve448.AArch64.Fast.limbs_loop (base := base) (outs := [o]) (rs := [.x4, .x5])
    (body := fun i => [ld .x4 (a + 8 * i), ld .x5 (b + 8 * i), .add .x .x4 .x4 (twoPReg i),
      .sub .x .x4 .x4 .x5, st .x4 (o + 8 * i)])
    (fun u => u.gpr .x0 = VG.Proof.Curve448.AArch64.Fast.K2 ∧ u.gpr .x2 = VG.Proof.Curve448.AArch64.Fast.K4)
    (fun u v ⟨h0, h2⟩ k => ⟨(k.1 _ (by decide)).trans h0, (k.1 _ (by decide)).trans h2⟩) (by decide)
    (fun _ i => word t.mem base (a + 8 * i) + VG.Proof.Curve448.AArch64.Fast.twoPW i - word t.mem base (b + 8 * i)) t
    (fun i hi u us ⟨h0, h2⟩ hm => WP.mono (VG.Proof.Curve448.AArch64.Fast.subStep_ok us hi ho ha hb ho8 ha8 hb8 h0 h2)
      fun w ⟨wm, wk⟩ => ⟨fun o' ho' => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ho'; subst ho'
          rw [wm, word, Mem.readW_writeW_self64, VG.Proof.Curve448.AArch64.Fast.away_word hm (by omega) (by simp; omega),
            VG.Proof.Curve448.AArch64.Fast.away_word hm (by omega) (by simp; omega)],
        fun x hx => by rw [wm]; exact VG.Proof.Curve448.AArch64.Fast.writeW_frame _ (by omega) _ x (hx o (by simp)), wk⟩)
    (by simp; omega) (by simp) ts ⟨t0, t2⟩
  refine WP.mono this fun u ⟨uv, um, uk⟩ => ⟨fun i hi => by rw [uv o (by simp) i hi, tm], fun x hx => by
    rw [um x hx, tm], (tk.mono (by decide)).trans (uk.mono (by decide))⟩

theorem addSubStep_ok {t : State} {base : Addr} (ht : Scr t base) {o₁ o₂ a b i : Nat} (hi : i < 8)
    (ho₁ : o₁ + 64 ≤ 8192) (ho₂ : o₂ + 64 ≤ 8192) (ha : a + 64 ≤ 8192) (hb : b + 64 ≤ 8192)
    (ho₁8 : o₁ % 8 = 0) (ho₂8 : o₂ % 8 = 0) (ha8 : a % 8 = 0) (hb8 : b % 8 = 0)
    (h0 : t.gpr .x0 = VG.Proof.Curve448.AArch64.Fast.K2) (h2 : t.gpr .x2 = VG.Proof.Curve448.AArch64.Fast.K4) :
    WP isa (.block [ld .x4 (a + 8 * i), ld .x5 (b + 8 * i), .add .x .x6 .x4 .x5, st .x6 (o₁ + 8 * i),
      .add .x .x7 .x4 (twoPReg i), .sub .x .x7 .x7 .x5, st .x7 (o₂ + 8 * i)]) t fun u =>
      u.mem = (t.mem.writeW (off base (o₁ + 8 * i))
        (word t.mem base (a + 8 * i) + word t.mem base (b + 8 * i))).writeW (off base (o₂ + 8 * i))
        (word t.mem base (a + 8 * i) + VG.Proof.Curve448.AArch64.Fast.twoPW i - word t.mem base (b + 8 * i)) ∧
      Keeps [.x4, .x5, .x6, .x7] t u := by
  obtain ⟨ra, aa, rb, ab⟩ := VG.Proof.Curve448.AArch64.Fast.ld2 ht (d := a + 8 * i) (e := b + 8 * i) (by omega) (by omega) (by omega)
    (by omega)
  have wo₁ := ht.write (d := o₁ + 8 * i) (n := 8) (by omega)
  have wo₂ := ht.write (d := o₂ + 8 * i) (n := 8) (by omega)
  have ao₁ : (o₁ + 8 * i) % 8 = 0 ∧ o₁ + 8 * i < 4096 * 8 := ⟨by omega, by omega⟩
  have ao₂ : (o₂ + 8 * i) % 8 = 0 ∧ o₂ + 8 * i < 4096 * 8 := ⟨by omega, by omega⟩
  have tw : twoPReg i ≠ .x4 ∧ twoPReg i ≠ .x5 ∧ twoPReg i ≠ .x6 ∧ twoPReg i ≠ .x7 := by
    simp only [twoPReg]; split <;> decide
  refine WP.of_runBlock ⟨_, by
    simp only [ld, st, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
      State.load, State.store, read_x, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write,
      RegUpd.wr_write, reduceCtorEq, ite_true, ite_false, ht.x3, aa, ab, ao₁, ao₂, ra, rb, wo₁, wo₂,
      and_self, Option.map_some, Option.bind_some]; rfl, ?_⟩
  refine ⟨?_, fun q hq => ?_, rfl, rfl⟩
  · simp only [tw.1, tw.2.1, tw.2.2.1, ite_false, BitVec.setWidth_eq, write8_eq, read8_eq,
      VG.Proof.Curve448.AArch64.Fast.twoPReg_val h0 h2]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp only [RegUpd.gpr_write, hq.1, hq.2.1, hq.2.2.1, hq.2.2.2, ite_false]

theorem addSub_ok {s : State} {base : Addr} (hs : Scr s base) {o₁ o₂ a b : Nat}
    (ho₁ : o₁ + 64 ≤ 8192) (ho₂ : o₂ + 64 ≤ 8192) (ha : a + 64 ≤ 8192) (hb : b + 64 ≤ 8192)
    (ho₁8 : o₁ % 8 = 0) (ho₂8 : o₂ % 8 = 0) (ha8 : a % 8 = 0) (hb8 : b % 8 = 0)
    (h12 : o₁ + 64 ≤ o₂ ∨ o₂ + 64 ≤ o₁) (h1a : o₁ + 64 ≤ a ∨ a + 64 ≤ o₁)
    (h1b : o₁ + 64 ≤ b ∨ b + 64 ≤ o₁) (h2a : o₂ + 64 ≤ a ∨ a + 64 ≤ o₂)
    (h2b : o₂ + 64 ≤ b ∨ b + 64 ≤ o₂) :
    WP isa (.block (Impl.Curve448.AArch64.Fast.addSub o₁ o₂ a b)) s fun t =>
      (∀ i < 8, word t.mem base (o₁ + 8 * i) = word s.mem base (a + 8 * i) + word s.mem base (b + 8 * i)) ∧
      (∀ i < 8, word t.mem base (o₂ + 8 * i) =
        word s.mem base (a + 8 * i) + VG.Proof.Curve448.AArch64.Fast.twoPW i - word s.mem base (b + 8 * i)) ∧
      (∀ x, VG.Proof.Curve448.AArch64.Fast.Away base [o₁, o₂] 64 x → t.mem x = s.mem x) ∧ Keeps [.x0, .x2, .x4, .x5, .x6, .x7] s t := by
  rw [Impl.Curve448.AArch64.Fast.addSub, WP.block_append_iff]
  refine WP.mono (VG.Proof.Curve448.AArch64.Fast.twoPRegs_ok s) fun t ⟨t0, t2, tm, tk⟩ => ?_
  have ts : Scr t base := hs.of_keeps tk (by decide)
  have ne : o₁ ≠ o₂ := by omega
  have := VG.Proof.Curve448.AArch64.Fast.limbs_loop (base := base) (outs := [o₁, o₂]) (rs := [.x4, .x5, .x6, .x7])
    (body := fun i => [ld .x4 (a + 8 * i), ld .x5 (b + 8 * i), .add .x .x6 .x4 .x5, st .x6 (o₁ + 8 * i),
      .add .x .x7 .x4 (twoPReg i), .sub .x .x7 .x7 .x5, st .x7 (o₂ + 8 * i)])
    (fun u => u.gpr .x0 = VG.Proof.Curve448.AArch64.Fast.K2 ∧ u.gpr .x2 = VG.Proof.Curve448.AArch64.Fast.K4)
    (fun u v ⟨h0, h2⟩ k => ⟨(k.1 _ (by decide)).trans h0, (k.1 _ (by decide)).trans h2⟩) (by decide)
    (fun o i => if o = o₁ then word t.mem base (a + 8 * i) + word t.mem base (b + 8 * i)
      else word t.mem base (a + 8 * i) + VG.Proof.Curve448.AArch64.Fast.twoPW i - word t.mem base (b + 8 * i)) t
    (fun i hi u us ⟨h0, h2⟩ hm => WP.mono (VG.Proof.Curve448.AArch64.Fast.addSubStep_ok us hi ho₁ ho₂ ha hb ho₁8 ho₂8 ha8 hb8 h0 h2)
      fun w ⟨wm, wk⟩ => ⟨fun o' ho' => by
          have ea := VG.Proof.Curve448.AArch64.Fast.away_word hm (d := a + 8 * i) (by omega) (by simp; omega)
          have eb := VG.Proof.Curve448.AArch64.Fast.away_word hm (d := b + 8 * i) (by omega) (by simp; omega)
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ho'
          rcases ho' with rfl | rfl
          · rw [wm, VG.Proof.Curve448.AArch64.Fast.word_writeW _ _ (by omega) (by omega) (by omega),
              ite_eq_right (by omega), word, Mem.readW_writeW_self64, ite_eq_left rfl, ea, eb]
          · rw [wm, word, Mem.readW_writeW_self64, ite_eq_right (Ne.symm ne), ea, eb],
        fun x hx => by
          rw [wm, VG.Proof.Curve448.AArch64.Fast.writeW_frame _ (by omega) _ x (hx o₂ (by simp)),
            VG.Proof.Curve448.AArch64.Fast.writeW_frame _ (by omega) _ x (hx o₁ (by simp))], wk⟩)
    (by simp; omega) (by simp; omega) ts ⟨t0, t2⟩
  refine WP.mono this fun u ⟨uv, um, uk⟩ => ⟨fun i hi => ?_, fun i hi => ?_, fun x hx => by
    rw [um x hx, tm], (tk.mono (by decide)).trans (uk.mono (by decide))⟩
  · rw [uv o₁ (by simp) i hi, ite_eq_left rfl, tm]
  · rw [uv o₂ (by simp) i hi, ite_eq_right (Ne.symm ne), tm]

end VG.Proof.Curve448.AArch64.Fast

end

/- Proofs formerly in `VerifiedGarbage.Proof.Curve448.AArch64.Fast.Butterfly`. -/
section

/-!
# The ladder's sums and differences, of conditionally swapped coordinates

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Curve448.AArch64.Fast

open VG VG.AArch64
open VG.Impl.Curve448.AArch64.Fast
open VG.Impl.X448.AArch64 (ld st ACC)
open VG.Proof.X448.AArch64 (Keeps Scr word off Outside writeW_outside limbs FieldMem ofs read8_eq
  write8_eq mask xor_sel)
open VG.Proof.Ed25519.AArch64 (read_x)

def bflyBody (x2 z2 x3 z3 a b c d i : Nat) : List Instr :=
  [ld .x4 (x2 + 8 * i), ld .x7 (x3 + 8 * i), ld .x5 (z2 + 8 * i), ld .x8 (z3 + 8 * i),
    .logic .eor .x .x9 .x4 .x7, .logic .and .x .x9 .x9 .x6,
    .logic .eor .x .x4 .x4 .x9, .logic .eor .x .x7 .x7 .x9,
    .logic .eor .x .x9 .x5 .x8, .logic .and .x .x9 .x9 .x6,
    .logic .eor .x .x5 .x5 .x9, .logic .eor .x .x8 .x8 .x9,
    .add .x .x9 .x4 .x5, st .x9 (a + 8 * i),
    .add .x .x10 .x4 (twoPReg i), .sub .x .x10 .x10 .x5, st .x10 (b + 8 * i),
    .add .x .x11 .x7 .x8, st .x11 (c + 8 * i),
    .add .x .x13 .x7 (twoPReg i), .sub .x .x13 .x13 .x8, st .x13 (d + 8 * i)]

theorem butterfly_split (x2 z2 x3 z3 a b c d : Nat) :
    butterfly x2 z2 x3 z3 a b c d = twoPRegs ++ (List.range 8).flatMap (VG.Proof.Curve448.AArch64.Fast.bflyBody x2 z2 x3 z3 a b c d) :=
  rfl

/-- The swapped words. -/
def sel (sw : Bool) (p q : BitVec 64) : BitVec 64 := if sw then q else p

theorem bflyStep_ok {t : State} {base : Addr} (ht : Scr t base) {x2 z2 x3 z3 a b c d i : Nat}
    (hi : i < 8) (h : ∀ e ∈ [x2, z2, x3, z3, a, b, c, d], e + 64 ≤ 8192 ∧ e % 8 = 0)
    (h0 : t.gpr .x0 = VG.Proof.Curve448.AArch64.Fast.K2) (h2 : t.gpr .x2 = VG.Proof.Curve448.AArch64.Fast.K4) {sw : Bool} (hm : t.gpr .x6 = VG.Proof.X448.AArch64.mask sw) :
    WP isa (.block (VG.Proof.Curve448.AArch64.Fast.bflyBody x2 z2 x3 z3 a b c d i)) t fun u =>
      let X2 := VG.Proof.Curve448.AArch64.Fast.sel sw (word t.mem base (x2 + 8 * i)) (word t.mem base (x3 + 8 * i))
      let X3 := VG.Proof.Curve448.AArch64.Fast.sel sw (word t.mem base (x3 + 8 * i)) (word t.mem base (x2 + 8 * i))
      let Z2 := VG.Proof.Curve448.AArch64.Fast.sel sw (word t.mem base (z2 + 8 * i)) (word t.mem base (z3 + 8 * i))
      let Z3 := VG.Proof.Curve448.AArch64.Fast.sel sw (word t.mem base (z3 + 8 * i)) (word t.mem base (z2 + 8 * i))
      u.mem = (((t.mem.writeW (off base (a + 8 * i)) (X2 + Z2)).writeW (off base (b + 8 * i))
        (X2 + VG.Proof.Curve448.AArch64.Fast.twoPW i - Z2)).writeW (off base (c + 8 * i)) (X3 + Z3)).writeW (off base (d + 8 * i))
        (X3 + VG.Proof.Curve448.AArch64.Fast.twoPW i - Z3) ∧
      Keeps [.x4, .x5, .x7, .x8, .x9, .x10, .x11, .x13] t u := by
  have g : ∀ e ∈ [x2, z2, x3, z3, a, b, c, d], (e + 8 * i) % 8 = 0 ∧ e + 8 * i < 4096 * 8 ∧
      InRegions (t.rd ++ t.wr) (base + BitVec.ofNat 64 (e + 8 * i)) 8 ∧
      InRegions t.wr (base + BitVec.ofNat 64 (e + 8 * i)) 8 := fun e he => by
    have := h e he
    exact ⟨by omega, by omega, ht.read (by omega), ht.write (by omega)⟩
  obtain ⟨ax2, bx2, rx2, -⟩ := g x2 (by simp)
  obtain ⟨az2, bz2, rz2, -⟩ := g z2 (by simp)
  obtain ⟨ax3, bx3, rx3, -⟩ := g x3 (by simp)
  obtain ⟨az3, bz3, rz3, -⟩ := g z3 (by simp)
  obtain ⟨aa, ba, -, wa⟩ := g a (by simp)
  obtain ⟨ab, bb, -, wb⟩ := g b (by simp)
  obtain ⟨ac, bc, -, wc⟩ := g c (by simp)
  obtain ⟨ad, bd, -, wd⟩ := g d (by simp)
  have tw : twoPReg i ≠ .x4 ∧ twoPReg i ≠ .x5 ∧ twoPReg i ≠ .x7 ∧ twoPReg i ≠ .x8 ∧
      twoPReg i ≠ .x9 ∧ twoPReg i ≠ .x10 ∧ twoPReg i ≠ .x11 := by
    simp only [twoPReg]; split <;> decide
  refine WP.of_runBlock ⟨_, by
    simp only [VG.Proof.Curve448.AArch64.Fast.bflyBody, ld, st, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
      State.load, State.store, read_x, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write,
      RegUpd.wr_write, reduceCtorEq, ite_true, ite_false, ht.x3, ax2, bx2, ax3, bx3, az2, bz2, az3, bz3,
      aa, ba, ab, bb, ac, bc, ad, bd, rx2, rx3, rz2, rz3, wa, wb, wc, wd, and_self, Option.map_some,
      Option.bind_some]; rfl, ?_⟩
  refine ⟨?_, fun q hq => ?_, rfl, rfl⟩
  · have sx := VG.Proof.X448.AArch64.xor_sel sw (word t.mem base (x2 + 8 * i)) (word t.mem base (x3 + 8 * i))
    have sz := VG.Proof.X448.AArch64.xor_sel sw (word t.mem base (z2 + 8 * i)) (word t.mem base (z3 + 8 * i))
    simp only [word, off] at sx sz
    simp only [tw.1, tw.2.1, tw.2.2.1, tw.2.2.2.1, tw.2.2.2.2.1,
      tw.2.2.2.2.2.1, tw.2.2.2.2.2.2, ite_false, BitVec.setWidth_eq, write8_eq,
      read8_eq, word, off, hm, sx.1, sx.2, sz.1, sz.2, VG.Proof.Curve448.AArch64.Fast.twoPReg_val h0 h2, VG.Proof.Curve448.AArch64.Fast.sel]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8⟩ := hq
    simp only [RegUpd.gpr_write, q1, q2, q3, q4, q5, q6, q7, q8, ite_false]

/-- Slots `x` and `y` (64 bytes each) are disjoint. -/
abbrev Dj (x y : Nat) : Prop := x + 64 ≤ y ∨ y + 64 ≤ x

theorem word_w4 (m : Mem) (base : Addr) {p q r t d : Nat} (v₁ v₂ v₃ v₄ : BitVec 64)
    (hp : p + 8 ≤ 8192) (hq : q + 8 ≤ 8192) (hr : r + 8 ≤ 8192) (ht : t + 8 ≤ 8192) (hd : d + 8 ≤ 8192)
    (sp : d = p ∨ d + 8 ≤ p ∨ p + 8 ≤ d) (sq : d = q ∨ d + 8 ≤ q ∨ q + 8 ≤ d)
    (sr : d = r ∨ d + 8 ≤ r ∨ r + 8 ≤ d) (st' : d = t ∨ d + 8 ≤ t ∨ t + 8 ≤ d) :
    word ((((m.writeW (off base p) v₁).writeW (off base q) v₂).writeW (off base r) v₃).writeW
      (off base t) v₄) base d =
      if d = t then v₄ else if d = r then v₃ else if d = q then v₂ else if d = p then v₁ else
        word m base d := by
  rw [VG.Proof.Curve448.AArch64.Fast.word_writeW _ _ ht hd st',
    VG.Proof.Curve448.AArch64.Fast.word_writeW _ _ hr hd sr,
    VG.Proof.Curve448.AArch64.Fast.word_writeW _ _ hq hd sq,
    VG.Proof.Curve448.AArch64.Fast.word_writeW _ _ hp hd sp]

def bflyV (m : Mem) (base : Addr) (sw : Bool) (x2 z2 x3 z3 a b c : Nat) (o i : Nat) : BitVec 64 :=
  let X2 := VG.Proof.Curve448.AArch64.Fast.sel sw (word m base (x2 + 8 * i)) (word m base (x3 + 8 * i))
  let X3 := VG.Proof.Curve448.AArch64.Fast.sel sw (word m base (x3 + 8 * i)) (word m base (x2 + 8 * i))
  let Z2 := VG.Proof.Curve448.AArch64.Fast.sel sw (word m base (z2 + 8 * i)) (word m base (z3 + 8 * i))
  let Z3 := VG.Proof.Curve448.AArch64.Fast.sel sw (word m base (z3 + 8 * i)) (word m base (z2 + 8 * i))
  if o = a then X2 + Z2 else if o = b then X2 + VG.Proof.Curve448.AArch64.Fast.twoPW i - Z2 else if o = c then X3 + Z3
  else X3 + VG.Proof.Curve448.AArch64.Fast.twoPW i - Z3

theorem butterfly_ok {s : State} {base : Addr} (hs : Scr s base) {x2 z2 x3 z3 a b c d : Nat}
    (h : ∀ e ∈ [x2, z2, x3, z3, a, b, c, d], e + 64 ≤ 8192 ∧ e % 8 = 0)
    (hout : ∀ o ∈ [a, b, c, d], ∀ o' ∈ [a, b, c, d], o ≠ o' → VG.Proof.Curve448.AArch64.Fast.Dj o o')
    (hin : ∀ o ∈ [a, b, c, d], ∀ e ∈ [x2, z2, x3, z3], VG.Proof.Curve448.AArch64.Fast.Dj o e)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    {sw : Bool} (hm : s.gpr .x6 = VG.Proof.X448.AArch64.mask sw) :
    WP isa (.block (butterfly x2 z2 x3 z3 a b c d)) s fun t =>
      (∀ o ∈ [a, b, c, d], ∀ i < 8, word t.mem base (o + 8 * i) = VG.Proof.Curve448.AArch64.Fast.bflyV s.mem base sw x2 z2 x3 z3 a b c o i) ∧
      (∀ x, VG.Proof.Curve448.AArch64.Fast.Away base [a, b, c, d] 64 x → t.mem x = s.mem x) ∧
      Keeps [.x0, .x2, .x4, .x5, .x7, .x8, .x9, .x10, .x11, .x13] s t := by
  rw [VG.Proof.Curve448.AArch64.Fast.butterfly_split, WP.block_append_iff]
  refine WP.mono (VG.Proof.Curve448.AArch64.Fast.twoPRegs_ok s) fun t ⟨t0, t2, tm, tk⟩ => ?_
  have ts : Scr t base := hs.of_keeps tk (by decide)
  have h6 : t.gpr .x6 = VG.Proof.X448.AArch64.mask sw := by rw [tk.1 _ (by decide), hm]
  have hb := fun e (he : e ∈ [x2, z2, x3, z3, a, b, c, d]) => h e he
  have ha' := hb a (by simp); have hb' := hb b (by simp); have hc' := hb c (by simp)
  have hd' := hb d (by simp)
  have dab := hout a (by simp) b (by simp) hab; have dac := hout a (by simp) c (by simp) hac
  have dad := hout a (by simp) d (by simp) had; have dbc := hout b (by simp) c (by simp) hbc
  have dbd := hout b (by simp) d (by simp) hbd; have dcd := hout c (by simp) d (by simp) hcd
  have := VG.Proof.Curve448.AArch64.Fast.limbs_loop (base := base) (outs := [a, b, c, d]) (rs := [.x4, .x5, .x7, .x8, .x9, .x10, .x11, .x13])
    (body := VG.Proof.Curve448.AArch64.Fast.bflyBody x2 z2 x3 z3 a b c d)
    (fun u => u.gpr .x0 = VG.Proof.Curve448.AArch64.Fast.K2 ∧ u.gpr .x2 = VG.Proof.Curve448.AArch64.Fast.K4 ∧ u.gpr .x6 = VG.Proof.X448.AArch64.mask sw)
    (fun u v ⟨h0, h2, h6⟩ k => ⟨(k.1 _ (by decide)).trans h0, (k.1 _ (by decide)).trans h2,
      (k.1 _ (by decide)).trans h6⟩) (by decide)
    (VG.Proof.Curve448.AArch64.Fast.bflyV t.mem base sw x2 z2 x3 z3 a b c) t
    (fun i hi u us ⟨h0, h2, h6⟩ hm' => WP.mono (VG.Proof.Curve448.AArch64.Fast.bflyStep_ok us hi h h0 h2 h6)
      fun w ⟨wm, wk⟩ => ⟨fun o' ho' => ?_, fun x hx => ?_, wk⟩)
    (fun o ho => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl <;> omega) hout ts ⟨t0, t2, h6⟩
  · refine WP.mono this fun u ⟨uv, um, uk⟩ => ⟨fun o ho i hi => ?_, fun x hx => by rw [um x hx, tm],
      (tk.mono (by decide)).trans (uk.mono (by decide))⟩
    rw [uv o ho i hi]; simp only [VG.Proof.Curve448.AArch64.Fast.bflyV, tm]
  · have e : ∀ q ∈ [x2, z2, x3, z3], word u.mem base (q + 8 * i) = word t.mem base (q + 8 * i) := by
      intro q hq
      have := (h q (List.mem_append_left [a, b, c, d] (by exact hq))).1
      exact VG.Proof.Curve448.AArch64.Fast.away_word hm' (by omega) (fun o ho => by have := hin o ho q hq; simp only [VG.Proof.Curve448.AArch64.Fast.Dj] at this; omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho'
    rw [wm]
    rcases ho' with rfl | rfl | rfl | rfl
    all_goals
      rw [VG.Proof.Curve448.AArch64.Fast.word_w4 _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)]
      simp only [VG.Proof.Curve448.AArch64.Fast.bflyV, e x2 (by simp), e z2 (by simp), e x3 (by simp), e z3 (by simp)]
    all_goals split_ifs <;> first | (exfalso; omega) | rfl
  · rw [wm]
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hx
    rw [VG.Proof.Curve448.AArch64.Fast.writeW_frame _ (by omega) _ x hx.2.2.2, VG.Proof.Curve448.AArch64.Fast.writeW_frame _ (by omega) _ x hx.2.2.1,
      VG.Proof.Curve448.AArch64.Fast.writeW_frame _ (by omega) _ x hx.2.1, VG.Proof.Curve448.AArch64.Fast.writeW_frame _ (by omega) _ x hx.1]

end VG.Proof.Curve448.AArch64.Fast

end

/- Proofs formerly in `VerifiedGarbage.Proof.Curve448.AArch64.Fast.Small`. -/
section

/-!
# `a + 39081 e`

Untrusted: everything here is checked by Lean. Limb `i` of the result is
`a_i + (39081 e_i mod 2⁵⁶) + c_{i-1}` (and `+ c₇` for limb 4), with
`c_i = ⌊39081 e_i / 2⁵⁶⌋` and `c_{-1} = c₇`.
-/

namespace VG.Proof.Curve448.AArch64.Fast

open VG VG.AArch64
open VG.Impl.Curve448.AArch64.Fast
open VG.Impl.X448.AArch64 (ld st ACC)
open VG.Proof.X448.Wide (radix)
open VG.Proof.X448.AArch64 (Keeps Scr word off Outside writeW_outside limbs FieldMem ofs read8_eq
  write8_eq)
open VG.Proof.Ed25519.AArch64 (read_x)

def smallRegs : List Reg :=
  [.x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x13, .x14, .x15, .x16, .x17, .x21, .x22, .x23, .x24]

theorem small_mem : ∀ i < 8, smallX i ∈ VG.Proof.Curve448.AArch64.Fast.smallRegs ∧ smallC i ∈ VG.Proof.Curve448.AArch64.Fast.smallRegs := by decide
theorem small_not : ∀ i < 8, smallX i ∉ [Reg.x0, .x2, .x24, .x3, .x12] ∧
    smallC i ∉ [Reg.x0, .x2, .x24, .x3, .x12] ∧ smallX i ≠ smallC i := by decide
theorem small_inj : ∀ i < 8, ∀ j < 8, j ≠ i → smallX j ≠ smallX i ∧ smallC j ≠ smallC i ∧
    smallX j ≠ smallC i ∧ smallC j ≠ smallX i := by decide

/-- The carry of limb `i`. -/
def sc (e : Nat → Nat) (i : Nat) : Nat := 39081 * e i / VG.Proof.X448.Wide.radix

/-- Limb `i` before the carries. -/
def sl (a e : Nat → Nat) (i : Nat) : Nat := a i + 39081 * e i % VG.Proof.X448.Wide.radix

theorem smallLimb_val (x e : BitVec 64) (hx : x.toNat + 2 ^ 56 ≤ 2 ^ 64) (he : e.toNat < 2 ^ 59) :
    (x + e * BitVec.ofNat 64 39081 - (BitVec.ofNat 64 (e.toNat * 10004736 / 2 ^ 64) <<< 56)).toNat =
      x.toNat + 39081 * e.toNat % VG.Proof.X448.Wide.radix ∧
    (BitVec.ofNat 64 (e.toNat * 10004736 / 2 ^ 64)).toNat = 39081 * e.toNat / VG.Proof.X448.Wide.radix := by
  have hc : e.toNat * 10004736 / 2 ^ 64 = 39081 * e.toNat / VG.Proof.X448.Wide.radix := by
    simp only [VG.Proof.X448.Wide.radix]; omega
  rw [hc]
  have hcl : 39081 * e.toNat / VG.Proof.X448.Wide.radix < 2 ^ 64 := by simp only [VG.Proof.X448.Wide.radix]; omega
  refine ⟨?_, by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hcl⟩
  generalize hl : 39081 * e.toNat % VG.Proof.X448.Wide.radix = l
  generalize hcc : 39081 * e.toNat / VG.Proof.X448.Wide.radix = c at hcl
  have hm : l + VG.Proof.X448.Wide.radix * c = 39081 * e.toNat := by rw [← hl, ← hcc]; exact Nat.mod_add_div _ _
  have hlt : l < VG.Proof.X448.Wide.radix := by rw [← hl]; exact Nat.mod_lt _ (by decide)
  have h1 : c * 2 ^ 56 % 2 ^ 64 = c % 2 ^ 8 * 2 ^ 56 := by
    rw [show (2 : Nat) ^ 64 = 2 ^ 8 * 2 ^ 56 by decide, Nat.mul_mod_mul_right]
  have h2 : e.toNat * 39081 % 2 ^ 64 = l + c % 2 ^ 8 * 2 ^ 56 := by
    rw [Nat.mul_comm, ← hm]
    simp only [VG.Proof.X448.Wide.radix] at hlt ⊢
    omega
  rw [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_shiftLeft,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mod_eq_of_lt hcl,
    show 39081 % 2 ^ 64 = 39081 by decide, h1, h2]
  simp only [VG.Proof.X448.Wide.radix] at hlt ⊢
  omega

def K39 : BitVec 64 := BitVec.ofNat 64 39081
def K8 : BitVec 64 := BitVec.ofNat 64 10004736

theorem smallConsts_ok (s : State) :
    WP isa (.block [.movz .x .x0 39081 0, .movz .x .x2 0xa900 0, .movk .x .x2 0x0098 1]) s fun t =>
      t.gpr .x0 = VG.Proof.Curve448.AArch64.Fast.K39 ∧ t.gpr .x2 = VG.Proof.Curve448.AArch64.Fast.K8 ∧ t.mem = s.mem ∧ Keeps [.x0, .x2] s t := by
  refine WP.of_runBlock ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
      show 16 * 0 < 64 from by decide, show 16 * 1 < 64 from by decide, ite_true]; rfl, ?_⟩
  refine ⟨?_, ?_, rfl, fun q hq => ?_, rfl, rfl⟩
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false]; decide
  · simp only [State.read, RegUpd.gpr_write, ite_true]; decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp only [RegUpd.gpr_write, hq.1, hq.2, ite_false]

theorem smallLimbStep_ok {t : State} {base : Addr} (ht : Scr t base) {a e i : Nat} (hi : i < 8)
    (ha : a + 64 ≤ 8192) (he : e + 64 ≤ 8192) (ha8 : a % 8 = 0) (he8 : e % 8 = 0)
    (h0 : t.gpr .x0 = VG.Proof.Curve448.AArch64.Fast.K39) (h2 : t.gpr .x2 = VG.Proof.Curve448.AArch64.Fast.K8) :
    WP isa (.block (smallLimb a e i)) t fun u =>
      u.gpr (smallX i) = word t.mem base (a + 8 * i) + word t.mem base (e + 8 * i) * VG.Proof.Curve448.AArch64.Fast.K39 -
        (BitVec.ofNat 64 ((word t.mem base (e + 8 * i)).toNat * 10004736 / 2 ^ 64) <<< 56) ∧
      u.gpr (smallC i) = BitVec.ofNat 64 ((word t.mem base (e + 8 * i)).toNat * 10004736 / 2 ^ 64) ∧
      u.mem = t.mem ∧ Keeps [.x24, smallX i, smallC i] t u := by
  obtain ⟨re, ae, ra, aa⟩ := VG.Proof.Curve448.AArch64.Fast.ld2 ht (d := e + 8 * i) (e := a + 8 * i) (by omega) (by omega) (by omega)
    (by omega)
  obtain ⟨n1, n2, n3⟩ := VG.Proof.Curve448.AArch64.Fast.small_not i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at n1 n2
  obtain ⟨x0, x2, x24, x3, -⟩ := n1
  obtain ⟨c0, c2, c24, c3, -⟩ := n2
  refine WP.of_runBlock ⟨_, by
    simp only [smallLimb, ld, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
      Size.bits, State.load, read_x, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write,
      RegUpd.wr_write, x24, Ne.symm x24, reduceCtorEq, ite_true, ite_false, ht.x3, ae, aa, re, ra, and_self,
      show 56 < 64 from by decide, Option.map_some, Option.bind_some]; rfl, ?_⟩
  refine ⟨?_, ?_, rfl, fun q hq => ?_, rfl, rfl⟩
  · have k8 : (BitVec.ofNat 64 10004736 : BitVec 64).toNat = 10004736 := rfl
    simp only [RegUpd.gpr_write, BitVec.setWidth_eq, ite_true, ite_false, x24,
      n3, Ne.symm x0, Ne.symm x2, read8_eq, h0, h2,
      VG.Proof.Curve448.AArch64.Fast.K8, k8]
  · have k8 : (BitVec.ofNat 64 10004736 : BitVec 64).toNat = 10004736 := rfl
    simp only [RegUpd.gpr_write, BitVec.setWidth_eq, ite_true, ite_false, c24,
      Ne.symm n3, n3, Ne.symm x2, read8_eq, h2, VG.Proof.Curve448.AArch64.Fast.K8, k8]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp only [RegUpd.gpr_write, hq.1, hq.2.1, hq.2.2, ite_false]

theorem smallLoop1_ok {s : State} {base : Addr} (hs : Scr s base) {a e : Nat}
    (ha : a + 64 ≤ 8192) (he : e + 64 ≤ 8192) (ha8 : a % 8 = 0) (he8 : e % 8 = 0)
    (h0 : s.gpr .x0 = VG.Proof.Curve448.AArch64.Fast.K39) (h2 : s.gpr .x2 = VG.Proof.Curve448.AArch64.Fast.K8) :
    WP isa (.block ((List.range 8).flatMap (smallLimb a e))) s fun t =>
      (∀ i < 8, t.gpr (smallX i) = word s.mem base (a + 8 * i) + word s.mem base (e + 8 * i) * VG.Proof.Curve448.AArch64.Fast.K39 -
        (BitVec.ofNat 64 ((word s.mem base (e + 8 * i)).toNat * 10004736 / 2 ^ 64) <<< 56)) ∧
      (∀ i < 8, t.gpr (smallC i) = BitVec.ofNat 64 ((word s.mem base (e + 8 * i)).toNat * 10004736 / 2 ^ 64)) ∧
      t.mem = s.mem ∧ Keeps VG.Proof.Curve448.AArch64.Fast.smallRegs s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, t.gpr (smallX i) = word s.mem base (a + 8 * i) + word s.mem base (e + 8 * i) * VG.Proof.Curve448.AArch64.Fast.K39 -
      (BitVec.ofNat 64 ((word s.mem base (e + 8 * i)).toNat * 10004736 / 2 ^ 64) <<< 56)) ∧
    (∀ i < n, t.gpr (smallC i) = BitVec.ofNat 64 ((word s.mem base (e + 8 * i)).toNat * 10004736 / 2 ^ 64)) ∧
    t.mem = s.mem ∧ Keeps VG.Proof.Curve448.AArch64.Fast.smallRegs s t
  refine wp_range_flatMap (M := isa) (N := 8) inv (fun n t hn ⟨tx, tc, tm, tk⟩ => ?_) 8 (by decide) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _), rfl, Keeps.refl _ _⟩
  have ts : Scr t base := hs.of_keeps tk (by decide)
  refine WP.mono (VG.Proof.Curve448.AArch64.Fast.smallLimbStep_ok ts hn ha he ha8 he8 ((tk.1 _ (by decide)).trans h0)
    ((tk.1 _ (by decide)).trans h2)) fun u ⟨ux, uc, um, uk⟩ => ?_
  have nk : ∀ i < 8, i ≠ n → smallX i ∉ [Reg.x24, smallX n, smallC n] ∧
      smallC i ∉ [Reg.x24, smallX n, smallC n] := by
    intro i hi h
    obtain ⟨q1, q2, -⟩ := VG.Proof.Curve448.AArch64.Fast.small_not i hi
    obtain ⟨r1, r2, r3, r4⟩ := VG.Proof.Curve448.AArch64.Fast.small_inj n hn i hi h
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at q1 q2 ⊢
    exact ⟨⟨q1.2.2.1, r1, r3⟩, ⟨q2.2.2.1, r4, r2⟩⟩
  refine ⟨fun i hi => ?_, fun i hi => ?_, um.trans tm, tk.trans (uk.mono fun r hr => ?_)⟩
  · by_cases h : i = n
    · subst h; rw [ux, tm]
    · rw [uk.1 _ (nk i (by omega) h).1, tx i (by omega)]
  · by_cases h : i = n
    · subst h; rw [uc, tm]
    · rw [uk.1 _ (nk i (by omega) h).2, tc i (by omega)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · exact (VG.Proof.Curve448.AArch64.Fast.small_mem n hn).1
    · exact (VG.Proof.Curve448.AArch64.Fast.small_mem n hn).2

def smallStore (o i : Nat) : List Instr :=
  [.add .x (smallX i) (smallX i) (smallC ((i + 7) % 8))] ++
    (if i = 4 then [.add .x (smallX i) (smallX i) (smallC 7)] else []) ++ [st (smallX i) (o + 8 * i)]

theorem small_split (o a e : Nat) :
    small o a e = ([.movz .x .x0 39081 0, .movz .x .x2 0xa900 0, .movk .x .x2 0x0098 1] : List Instr) ++
      (List.range 8).flatMap (smallLimb a e) ++ (List.range 8).flatMap (VG.Proof.Curve448.AArch64.Fast.smallStore o) := rfl

/-- The value `smallStore` writes. -/
def smallOut (X C : Nat → BitVec 64) (i : Nat) : BitVec 64 :=
  X i + C ((i + 7) % 8) + if i = 4 then C 7 else 0

theorem smallCX : ∀ i < 8, smallC ((i + 7) % 8) ≠ smallX i ∧ smallC 7 ≠ smallX i := by decide

theorem smallStore_ok {t : State} {base : Addr} (ht : Scr t base) {o i : Nat} (hi : i < 8)
    (ho : o + 64 ≤ 8192) (ho8 : o % 8 = 0) :
    WP isa (.block (VG.Proof.Curve448.AArch64.Fast.smallStore o i)) t fun u =>
      (∀ d, d + 8 ≤ 8192 → (d = o + 8 * i ∨ d + 8 ≤ o + 8 * i ∨ o + 8 * i + 8 ≤ d) →
        word u.mem base d = if d = o + 8 * i then VG.Proof.Curve448.AArch64.Fast.smallOut (fun j => t.gpr (smallX j)) (fun j => t.gpr (smallC j)) i else word t.mem base d) ∧
      Outside base (o + 8 * i) 8 t.mem u.mem ∧ Keeps [smallX i] t u := by
  obtain ⟨cx, c7⟩ := VG.Proof.Curve448.AArch64.Fast.smallCX i hi
  have hx3 := (VG.Proof.Curve448.AArch64.Fast.small_not i hi).1
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx3
  by_cases h4 : i = 4
  · subst h4
    simp only [VG.Proof.Curve448.AArch64.Fast.smallStore, ite_true, List.cons_append, List.nil_append]
    rw [show [Instr.add .x (smallX 4) (smallX 4) (smallC ((4 + 7) % 8)),
        .add .x (smallX 4) (smallX 4) (smallC 7), st (smallX 4) (o + 8 * 4)] =
        [Instr.add .x (smallX 4) (smallX 4) (smallC ((4 + 7) % 8))] ++
        [Instr.add .x (smallX 4) (smallX 4) (smallC 7)] ++ [st (smallX 4) (o + 8 * 4)] from rfl,
      List.append_assoc, WP.block_append_iff]
    refine WP.mono (VG.Proof.Curve448.AArch64.Fast.add_ok t _ _ _) fun u ⟨uv, um, uk⟩ => ?_
    rw [WP.block_append_iff]
    refine WP.mono (VG.Proof.Curve448.AArch64.Fast.add_ok u _ _ _) fun v ⟨vv, vm, vk⟩ => ?_
    have vs : Scr v base := (ht.of_keeps uk (by simp only [List.mem_cons, List.not_mem_nil, or_false]; exact ⟨Ne.symm hx3.2.2.2.1, Ne.symm hx3.2.2.2.2⟩)).of_keeps vk
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]; exact ⟨Ne.symm hx3.2.2.2.1, Ne.symm hx3.2.2.2.2⟩)
    refine WP.mono (VG.Proof.Curve448.AArch64.Fast.stw_ok vs _ (d := o + 8 * 4) (by omega) (by omega))
      fun w ⟨ww, wo, wg, wr, wwr⟩ => ⟨fun d hd hs => ?_, by rw [← um, ← vm]; exact wo,
        ⟨fun q hq => ?_, wr.trans (vk.2.1.trans uk.2.1), wwr.trans (vk.2.2.trans uk.2.2)⟩⟩
    · rw [ww d hd hs, vv, vm, um, uk.1 (smallC 7) (by simp only [List.mem_cons, List.not_mem_nil, or_false]; exact c7), uv]
      by_cases e : d = o + 8 * 4
      · rw [ite_eq_left e, ite_eq_left e]; simp only [VG.Proof.Curve448.AArch64.Fast.smallOut, ite_true]
      · rw [ite_eq_right e, ite_eq_right e]
    · rw [wg, vk.1 q hq, uk.1 q hq]
  · simp only [VG.Proof.Curve448.AArch64.Fast.smallStore, h4, ite_false, List.append_nil]
    rw [show [Instr.add .x (smallX i) (smallX i) (smallC ((i + 7) % 8))] ++ [st (smallX i) (o + 8 * i)] =
        [Instr.add .x (smallX i) (smallX i) (smallC ((i + 7) % 8))] ++ [st (smallX i) (o + 8 * i)] from rfl,
      WP.block_append_iff]
    refine WP.mono (VG.Proof.Curve448.AArch64.Fast.add_ok t _ _ _) fun u ⟨uv, um, uk⟩ => ?_
    have us : Scr u base := ht.of_keeps uk (by simp only [List.mem_cons, List.not_mem_nil, or_false]; exact ⟨Ne.symm hx3.2.2.2.1, Ne.symm hx3.2.2.2.2⟩)
    refine WP.mono (VG.Proof.Curve448.AArch64.Fast.stw_ok us _ (d := o + 8 * i) (by omega) (by omega))
      fun w ⟨ww, wo, wg, wr, wwr⟩ => ⟨fun d hd hs => ?_, by rw [← um]; exact wo,
        ⟨fun q hq => ?_, wr.trans uk.2.1, wwr.trans uk.2.2⟩⟩
    · rw [ww d hd hs, uv, um]
      by_cases e : d = o + 8 * i
      · rw [ite_eq_left e, ite_eq_left e]; simp only [VG.Proof.Curve448.AArch64.Fast.smallOut, h4, ite_false]; exact (BitVec.add_zero _).symm
      · rw [ite_eq_right e, ite_eq_right e]
    · rw [wg, uk.1 q hq]

theorem smallLoop2_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat} (ho : o + 64 ≤ 8192)
    (ho8 : o % 8 = 0) :
    WP isa (.block ((List.range 8).flatMap (VG.Proof.Curve448.AArch64.Fast.smallStore o))) s fun t =>
      (∀ i < 8, word t.mem base (o + 8 * i) =
        VG.Proof.Curve448.AArch64.Fast.smallOut (fun j => s.gpr (smallX j)) (fun j => s.gpr (smallC j)) i) ∧
      Outside base o 64 s.mem t.mem ∧ Keeps VG.Proof.Curve448.AArch64.Fast.smallRegs s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, word t.mem base (o + 8 * i) =
      VG.Proof.Curve448.AArch64.Fast.smallOut (fun j => s.gpr (smallX j)) (fun j => s.gpr (smallC j)) i) ∧
    (∀ i < 8, n ≤ i → t.gpr (smallX i) = s.gpr (smallX i)) ∧
    (∀ i < 8, t.gpr (smallC i) = s.gpr (smallC i)) ∧
    Outside base o (8 * n) s.mem t.mem ∧ Keeps VG.Proof.Curve448.AArch64.Fast.smallRegs s t
  refine WP.mono (wp_range_flatMap (M := isa) (N := 8) inv (fun n t hn ⟨tv, tx, tc, tO, tk⟩ => ?_) 8
    (by decide) s ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ => rfl, fun _ _ => rfl,
      Outside.refl _ _ _ _, Keeps.refl _ _⟩) fun t ⟨tv, _, _, tO, tk⟩ => ⟨tv, tO, tk⟩
  have ts : Scr t base := hs.of_keeps tk (by decide)
  refine WP.mono (VG.Proof.Curve448.AArch64.Fast.smallStore_ok ts hn ho ho8) fun u ⟨uw, uO, uk⟩ => ⟨fun i hi => ?_, fun i hi hni => ?_,
    fun i hi => ?_, ?_, tk.trans (uk.mono fun r hr => ?_)⟩
  · rw [uw _ (by omega) (by omega)]
    by_cases h : i = n
    · subst h
      rw [ite_eq_left rfl]
      simp only [VG.Proof.Curve448.AArch64.Fast.smallOut, tx i hn (Nat.le_refl _), tc _ (Nat.mod_lt _ (by decide)), tc 7 (by decide)]
    · rw [ite_eq_right (by omega)]; exact tv i (by omega)
  · have := (VG.Proof.Curve448.AArch64.Fast.small_inj n hn i hi (by omega)).1
    rw [uk.1 _ (by simp [this]), tx i hi (by omega)]
  · by_cases h : i = n
    · subst h; rw [uk.1 _ (by simp [(VG.Proof.Curve448.AArch64.Fast.small_not i hi).2.2.symm]), tc i hi]
    · rw [uk.1 _ (by simp [(VG.Proof.Curve448.AArch64.Fast.small_inj n hn i hi h).2.2.2]), tc i hi]
  · rw [show 8 * (n + 1) = 8 * n + 8 by omega]
    intro x hx
    rw [uO x (by omega), tO x (by omega)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [hr]; exact (VG.Proof.Curve448.AArch64.Fast.small_mem n hn).1

/-- The limbs `small` writes, from the operands' limbs. -/
def smallVal (a e : Nat → Nat) (i : Nat) : Nat :=
  VG.Proof.Curve448.AArch64.Fast.sl a e i + VG.Proof.Curve448.AArch64.Fast.sc e ((i + 7) % 8) + if i = 4 then VG.Proof.Curve448.AArch64.Fast.sc e 7 else 0

theorem small_ok {s : State} {base : Addr} (hs : Scr s base) {o a e : Nat}
    (ho : o + 64 ≤ 8192) (ha : a + 64 ≤ 8192) (he : e + 64 ≤ 8192) (ho8 : o % 8 = 0) (ha8 : a % 8 = 0)
    (he8 : e % 8 = 0) (fa : ∀ i < 8, limbs s.mem base a i < VG.Proof.Curve448.AArch64.Fast.Mb) (fe : ∀ i < 8, limbs s.mem base e i < VG.Proof.Curve448.AArch64.Fast.Ib) :
    WP isa (.block (small o a e)) s fun t =>
      (∀ i < 8, limbs t.mem base o i = VG.Proof.Curve448.AArch64.Fast.smallVal (limbs s.mem base a) (limbs s.mem base e) i) ∧
      Outside base o 64 s.mem t.mem ∧ Keeps (.x0 :: .x2 :: VG.Proof.Curve448.AArch64.Fast.smallRegs) s t := by
  rw [VG.Proof.Curve448.AArch64.Fast.small_split, List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.Curve448.AArch64.Fast.smallConsts_ok s) fun t ⟨t0, t2, tm, tk⟩ => ?_
  have ts : Scr t base := hs.of_keeps tk (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Curve448.AArch64.Fast.smallLoop1_ok ts ha he ha8 he8 t0 t2) fun u ⟨ux, uc, um, uk⟩ => ?_
  have us : Scr u base := ts.of_keeps uk (by decide)
  refine WP.mono (VG.Proof.Curve448.AArch64.Fast.smallLoop2_ok us ho ho8) fun w ⟨wv, wo, wk⟩ => ⟨fun i hi => ?_, ?_,
    (tk.mono (by decide)).trans ((uk.mono (by decide)).trans (wk.mono (by decide)))⟩
  · have lv : ∀ j < 8, (u.gpr (smallX j)).toNat = VG.Proof.Curve448.AArch64.Fast.sl (limbs s.mem base a) (limbs s.mem base e) j ∧
        (u.gpr (smallC j)).toNat = VG.Proof.Curve448.AArch64.Fast.sc (limbs s.mem base e) j := by
      intro j hj
      have hb := fa j hj; have hb' := fe j hj
      simp only [VG.Proof.Curve448.AArch64.Fast.Mb, VG.Proof.Curve448.AArch64.Fast.Ib] at hb hb'
      have := VG.Proof.Curve448.AArch64.Fast.smallLimb_val (word s.mem base (a + 8 * j)) (word s.mem base (e + 8 * j))
        (by simp only [limbs] at hb; omega) (by simp only [limbs] at hb'; omega)
      rw [ux j hj, uc j hj, tm]
      exact this
    have hc : ∀ j < 8, VG.Proof.Curve448.AArch64.Fast.sc (limbs s.mem base e) j < 2 ^ 20 := by
      intro j hj; have := fe j hj; simp only [VG.Proof.Curve448.AArch64.Fast.sc, VG.Proof.Curve448.AArch64.Fast.Ib, VG.Proof.X448.Wide.radix] at this ⊢; omega
    have hsl : VG.Proof.Curve448.AArch64.Fast.sl (limbs s.mem base a) (limbs s.mem base e) i < 2 ^ 58 := by
      have := fa i hi; have := Nat.mod_lt (39081 * limbs s.mem base e i) (show 0 < VG.Proof.X448.Wide.radix by decide)
      simp only [VG.Proof.Curve448.AArch64.Fast.sl, VG.Proof.Curve448.AArch64.Fast.Mb, VG.Proof.X448.Wide.radix] at *; omega
    change (word w.mem base (o + 8 * i)).toNat = _
    rw [wv i hi]
    simp only [VG.Proof.Curve448.AArch64.Fast.smallOut, VG.Proof.Curve448.AArch64.Fast.smallVal]
    have h7 := (lv 7 (by decide)).2
    have hj := (lv ((i + 7) % 8) (Nat.mod_lt _ (by decide))).2
    have hx := (lv i hi).1
    have c7 := hc 7 (by decide)
    have cj := hc ((i + 7) % 8) (Nat.mod_lt _ (by decide))
    split
    · rw [BitVec.toNat_add, BitVec.toNat_add, hx, hj, h7]
      omega
    · rw [BitVec.toNat_add, BitVec.toNat_add, hx, hj, show (0 : BitVec 64).toNat = 0 from rfl]
      omega
  · intro x hx
    rw [wo x hx, um, tm]

end VG.Proof.Curve448.AArch64.Fast

end

/- Proofs formerly in `VerifiedGarbage.Proof.Curve448.AArch64.Fast.Field`. -/
section

/-!
# The field operations, modulo `p`

Untrusted: everything here is checked by Lean. Reduced elements (`Mb`)
are the outputs of products and the inputs of sums and differences; products
take any limbs below `Ib`, which sums, differences and `a + a24 e` keep.
-/

namespace VG.Proof.Curve448.AArch64.Fast

open VG VG.Spec.X448
open VG.Impl.Curve448.AArch64.Fast
open VG.Proof.X448 (toFe toFe_mul toFe_add toFe_sub toFe_congr)
open VG.Proof.X448.Wide (radix valN valN_congr valN_add rows reduced reduced_mod rows_val)

theorem Mb_le_Ib : VG.Proof.Curve448.AArch64.Fast.Mb ≤ VG.Proof.Curve448.AArch64.Fast.Ib := by decide

theorem prod_val (f g : Nat → Nat) :
    VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN (VG.Proof.Curve448.AArch64.Fast.prodOut f g) 8) = VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN f 8) * VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN g 8) := by
  apply VG.Proof.X448.toFe_mul
  rw [VG.Proof.Curve448.AArch64.Fast.out_mod, VG.Proof.X448.Wide.reduced_mod, rows_val f g (by decide)]

theorem prod_bound {f g : Nat → Nat} (hf : ∀ i < 8, f i < VG.Proof.Curve448.AArch64.Fast.Ib) (hg : ∀ i < 8, g i < VG.Proof.Curve448.AArch64.Fast.Ib) :
    ∀ i < 8, VG.Proof.Curve448.AArch64.Fast.prodOut f g i < VG.Proof.Curve448.AArch64.Fast.Mb := (VG.Proof.Curve448.AArch64.Fast.fits_of hf hg).out

theorem twoP_val : VG.Proof.X448.Wide.valN twoP 8 = 2 * VG.Spec.X448.P := by decide +kernel

theorem twoP_le (i : Nat) : VG.Proof.Curve448.AArch64.Fast.Mb ≤ twoP i := by simp only [twoP, VG.Proof.Curve448.AArch64.Fast.Mb]; split <;> omega

theorem twoPW_toNat (i : Nat) : (VG.Proof.Curve448.AArch64.Fast.twoPW i).toNat = twoP i := by
  simp only [VG.Proof.Curve448.AArch64.Fast.twoPW, twoP, VG.Proof.Curve448.AArch64.Fast.K2, VG.Proof.Curve448.AArch64.Fast.K4]; split <;> rfl

/-- `a + 2p - b`, for reduced `b`. -/
def diffN (f g : Nat → Nat) (i : Nat) : Nat := f i + twoP i - g i

theorem diff_val {f g : Nat → Nat} (hg : ∀ i < 8, g i < VG.Proof.Curve448.AArch64.Fast.Mb) :
    VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN (VG.Proof.Curve448.AArch64.Fast.diffN f g) 8) = VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN f 8) - VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN g 8) := by
  apply VG.Proof.X448.toFe_sub
  have : VG.Proof.X448.Wide.valN (VG.Proof.Curve448.AArch64.Fast.diffN f g) 8 + VG.Proof.X448.Wide.valN g 8 = VG.Proof.X448.Wide.valN f 8 + 2 * VG.Spec.X448.P := by
    rw [← VG.Proof.X448.Wide.valN_add, ← VG.Proof.Curve448.AArch64.Fast.twoP_val, ← VG.Proof.X448.Wide.valN_add]
    apply VG.Proof.X448.Wide.valN_congr
    intro i hi
    have := hg i hi; have := VG.Proof.Curve448.AArch64.Fast.twoP_le i
    simp only [VG.Proof.Curve448.AArch64.Fast.diffN]; omega
  rw [this, Nat.add_mul_mod_self_right]

theorem diff_bound {f g : Nat → Nat} (hf : ∀ i < 8, f i < VG.Proof.Curve448.AArch64.Fast.Mb) : ∀ i < 8, VG.Proof.Curve448.AArch64.Fast.diffN f g i < VG.Proof.Curve448.AArch64.Fast.Ib := by
  intro i hi
  have := hf i hi
  simp only [VG.Proof.Curve448.AArch64.Fast.diffN, twoP, VG.Proof.Curve448.AArch64.Fast.Mb, VG.Proof.Curve448.AArch64.Fast.Ib] at *
  split <;> omega

theorem diff_word (x y : BitVec 64) (i : Nat) (hx : x.toNat < VG.Proof.Curve448.AArch64.Fast.Mb) (hy : y.toNat < VG.Proof.Curve448.AArch64.Fast.Mb) :
    (x + VG.Proof.Curve448.AArch64.Fast.twoPW i - y).toNat = x.toNat + twoP i - y.toNat := by
  have := VG.Proof.Curve448.AArch64.Fast.twoP_le i
  have h2 : twoP i < 2 ^ 58 := by simp only [twoP]; split <;> omega
  simp only [VG.Proof.Curve448.AArch64.Fast.Mb] at hx hy this
  rw [BitVec.toNat_sub, BitVec.toNat_add, VG.Proof.Curve448.AArch64.Fast.twoPW_toNat]
  have := y.isLt
  simp only [Nat.reducePow] at *
  omega

theorem sum_val (f g : Nat → Nat) :
    VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN (fun i => f i + g i) 8) = VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN f 8) + VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN g 8) := by
  apply VG.Proof.X448.toFe_add; rw [VG.Proof.X448.Wide.valN_add]

theorem sum_bound {f g : Nat → Nat} (hf : ∀ i < 8, f i < VG.Proof.Curve448.AArch64.Fast.Mb) (hg : ∀ i < 8, g i < VG.Proof.Curve448.AArch64.Fast.Mb) :
    ∀ i < 8, f i + g i < VG.Proof.Curve448.AArch64.Fast.Ib := by
  intro i hi; have := hf i hi; have := hg i hi; simp only [VG.Proof.Curve448.AArch64.Fast.Mb, VG.Proof.Curve448.AArch64.Fast.Ib] at *; omega

theorem sum_word (x y : BitVec 64) (hx : x.toNat < VG.Proof.Curve448.AArch64.Fast.Mb) (hy : y.toNat < VG.Proof.Curve448.AArch64.Fast.Mb) :
    (x + y).toNat = x.toNat + y.toNat := by
  simp only [VG.Proof.Curve448.AArch64.Fast.Mb] at hx hy
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]

theorem small_val (f g : Nat → Nat) :
    VG.Proof.X448.Wide.valN (VG.Proof.Curve448.AArch64.Fast.smallVal f g) 8 + VG.Spec.X448.P * VG.Proof.Curve448.AArch64.Fast.sc g 7 = VG.Proof.X448.Wide.valN f 8 + 39081 * VG.Proof.X448.Wide.valN g 8 := by
  have hs : ∀ i, VG.Proof.Curve448.AArch64.Fast.sl f g i + VG.Proof.X448.Wide.radix * VG.Proof.Curve448.AArch64.Fast.sc g i = f i + 39081 * g i := fun i => by
    simp only [VG.Proof.Curve448.AArch64.Fast.sl, VG.Proof.Curve448.AArch64.Fast.sc]; have := Nat.mod_add_div (39081 * g i) VG.Proof.X448.Wide.radix; omega
  have h0 := hs 0; have h1 := hs 1; have h2 := hs 2; have h3 := hs 3
  have h4 := hs 4; have h5 := hs 5; have h6 := hs 6; have h7 := hs 7
  have hp : VG.Spec.X448.P = VG.Proof.X448.Wide.radix ^ 8 - VG.Proof.X448.Wide.radix ^ 4 - 1 := by decide +kernel
  simp only [VG.Proof.X448.Wide.valN, VG.Proof.Curve448.AArch64.Fast.smallVal, Nat.reduceAdd, Nat.reduceMod, ite_true, ite_false,
    show ¬ (0 = 4) by decide, show ¬ (1 = 4) by decide, show ¬ (2 = 4) by decide,
    show ¬ (3 = 4) by decide, show ¬ (5 = 4) by decide, show ¬ (6 = 4) by decide,
    show ¬ (7 = 4) by decide, Nat.zero_add, Nat.add_zero, Nat.pow_zero, Nat.one_mul]
  simp only [hp, VG.Proof.X448.Wide.radix, Nat.reducePow] at h0 h1 h2 h3 h4 h5 h6 h7 ⊢
  omega

theorem smallF (f g : Nat → Nat) :
    VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN (VG.Proof.Curve448.AArch64.Fast.smallVal f g) 8) = VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN f 8) + VG.Spec.X448.a24 * VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN g 8) := by
  have : VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN (VG.Proof.Curve448.AArch64.Fast.smallVal f g) 8) = VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN f 8 + 39081 * VG.Proof.X448.Wide.valN g 8) := by
    apply VG.Proof.X448.toFe_congr; rw [← VG.Proof.Curve448.AArch64.Fast.small_val, Nat.add_mul_mod_self_left]
  rw [this]
  exact VG.Proof.X448.toFe_add (b := 39081 * VG.Proof.X448.Wide.valN g 8) rfl |>.trans (congrArg _ (VG.Proof.X448.toFe_mul rfl))

theorem small_bound {f g : Nat → Nat} (hf : ∀ i < 8, f i < VG.Proof.Curve448.AArch64.Fast.Mb) (hg : ∀ i < 8, g i < VG.Proof.Curve448.AArch64.Fast.Ib) :
    ∀ i < 8, VG.Proof.Curve448.AArch64.Fast.smallVal f g i < VG.Proof.Curve448.AArch64.Fast.Ib := by
  intro i hi
  have hc : ∀ j < 8, VG.Proof.Curve448.AArch64.Fast.sc g j < 2 ^ 20 := fun j hj => by
    have := hg j hj; simp only [VG.Proof.Curve448.AArch64.Fast.sc, VG.Proof.Curve448.AArch64.Fast.Ib, VG.Proof.X448.Wide.radix] at *; omega
  have := hf i hi
  have hl := Nat.mod_lt (39081 * g i) (show 0 < VG.Proof.X448.Wide.radix by decide)
  have := hc ((i + 7) % 8) (Nat.mod_lt _ (by decide))
  have := hc 7 (by decide)
  simp only [VG.Proof.Curve448.AArch64.Fast.smallVal, VG.Proof.Curve448.AArch64.Fast.sl, VG.Proof.Curve448.AArch64.Fast.Mb, VG.Proof.Curve448.AArch64.Fast.Ib, VG.Proof.X448.Wide.radix] at *
  split <;> omega

end VG.Proof.Curve448.AArch64.Fast

end
