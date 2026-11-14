module

public import VerifiedGarbage.Proof.MlDsa.Arith.Mont
import VerifiedGarbage.Proof.Framework.Omega

/-! Integer bounds and residues for the private lazy ARM64 arithmetic. -/

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Arith

/-- Three-instruction positive normalization of a signed lane. -/
def positive (x : Int) : Int := x - x / 8388608 * 8380417 + 8380417

/-- The signed reduction used before signing checks. -/
def reduce32 (x : Int) : Int := x - (x + 4194304) / 8388608 * 8380417

theorem positive_bounds {x : Int} (hl : -2147483648 ≤ x) (hh : x < 2147483648) :
    6283521 ≤ positive x ∧ positive x ≤ 18857729 := by
  unfold positive
  omega_using [hl, hh]

theorem positive_lt_three_q {x : Int} (hl : -2147483648 ≤ x) (hh : x < 2147483648) :
    0 ≤ positive x ∧ positive x < 3 * (q : Int) := by
  have h := positive_bounds hl hh
  change 0 ≤ positive x ∧ positive x < 3 * (8380417 : Int)
  omega_using [h]

theorem positive_mod (x : Int) : positive x % 8380417 = x % 8380417 := by
  unfold positive
  omega_using []

theorem reduce32_bounds {x : Int} (hl : -2 * 8380417 < x) (hh : x < 3 * 8380417) :
    -4202495 ≤ reduce32 x ∧ reduce32 x ≤ 4210685 := by
  unfold reduce32
  omega_using [hl, hh]

theorem reduce32_mod (x : Int) : reduce32 x % 8380417 = x % 8380417 := by
  unfold reduce32
  omega_using []

/-- The exact signed high-product multiplier for a root in ordinary field form. -/
def reciprocal (z : Int) : Int := z * 2147483648 / 8380417

def fastMul (x z : Int) : Int := x * z - (x * reciprocal z / 2147483648) * 8380417

theorem reciprocal_bounds {z : Int} (hl : 0 ≤ z) (hh : z < 8380417) :
    0 ≤ reciprocal z ∧ reciprocal z < 2147483648 := by
  unfold reciprocal
  omega_using [hl, hh]

theorem reciprocal_remainder (z : Int) :
    0 ≤ z * 2147483648 - reciprocal z * 8380417 ∧
      z * 2147483648 - reciprocal z * 8380417 < 8380417 := by
  unfold reciprocal
  omega_using []

theorem fastMul_bounds {x z : Int} (hl : -2147483648 ≤ x) (hh : x < 2147483648) :
    -8380417 < fastMul x z ∧ fastMul x z < 2 * 8380417 := by
  let r := z * 2147483648 - reciprocal z * 8380417
  let t := x * reciprocal z - (x * reciprocal z / 2147483648) * 2147483648
  have hr : 0 ≤ r ∧ r < 8380417 := reciprocal_remainder z
  have ht : 0 ≤ t ∧ t < 2147483648 := by dsimp only [t]; omega_using []
  have he : 2147483648 * fastMul x z = x * r + 8380417 * t := by
    dsimp only [fastMul, r, t]
    simp only [Int.mul_sub]
    simp only [Int.mul_assoc,Int.mul_left_comm,Int.mul_comm]
    omega_using []
  have hlow := Int.mul_nonneg (by omega_using [hl] : 0 ≤ x + 2147483648) hr.1
  have hupp := Int.mul_nonneg (by omega_using [hh] : 0 ≤ 2147483648 - x) hr.1
  rw [Int.add_mul] at hlow
  rw [Int.sub_mul] at hupp
  omega_using [hr, he, hlow, hupp]

theorem fastMul_mod (x z : Int) : fastMul x z % 8380417 = (x * z) % 8380417 := by
  unfold fastMul
  omega_using []

/-- Both lazy factors fit the unsigned Montgomery product premise. -/
theorem product_lt_qR {a b : Nat} (ha : a < 3 * q) (hb : b < 3 * q) :
    a * b < q * 2 ^ 32 := by
  have h := Nat.mul_lt_mul'' ha hb
  exact Nat.lt_trans h (by decide)

theorem product_lt_nine_q2 {a b : Nat} (ha : a < 3 * q) (hb : b < 3 * q) :
    a * b < 9 * q ^ 2 := by
  have h := Nat.mul_lt_mul'' ha hb
  have he : 3*q*(3*q) = 9*q^2 := by decide
  rwa [he] at h

theorem mont_center_bounds {t : Nat} (ht : t < 9 * q ^ 2) :
    -(q : Int) ≤ (mont t : Int) - q ∧ (mont t : Int) - q ≤ 147168 := by
  have he := mont_mul t
  have hm := montM_lt t
  change t < 9 * 8380417 ^ 2 at ht
  change mont t * 4294967296 = t + montM t * 8380417 at he
  change montM t < 4294967296 at hm
  change -(8380417 : Int) ≤ (mont t : Int) - 8380417 ∧
    (mont t : Int) - 8380417 ≤ 147168
  omega_using [ht, he, hm]

end VG.Proof.MlDsa.AArch64.Optimized
