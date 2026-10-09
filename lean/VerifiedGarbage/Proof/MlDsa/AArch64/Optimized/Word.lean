import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Arithmetic
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Word

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG.AArch64
open VG.Spec.MlDsa (q)
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith.Neon

/-- Actual lane expression computed by SSHR, MLS, ADD. -/
def positiveWord (x : BitVec 32) : BitVec 32 :=
  x - x.sshiftRight 23 * BitVec.ofNat 32 q + BitVec.ofNat 32 q

theorem positiveWord_eq (x : BitVec 32) :
    positiveWord x = BitVec.ofInt 32 (positive x.toInt) := by
  unfold positiveWord positive
  rw [Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_add, BitVec.ofInt_neg,
    BitVec.ofInt_mul, BitVec.ofInt_toInt]
  have h : BitVec.ofInt 32 (x.toInt / 8388608) = x.sshiftRight 23 := by
    have ht := BitVec.toInt_sshiftRight (x := x) (n := 23)
    rw [Int.shiftRight_eq_div_pow] at ht
    change (x.sshiftRight 23).toInt = x.toInt / 8388608 at ht
    rw [← ht, BitVec.ofInt_toInt]
  rw [h]
  change x - x.sshiftRight 23 * 8380417#32 + 8380417#32 =
    x + -(x.sshiftRight 23 * 8380417#32) + 8380417#32
  rw [BitVec.sub_eq_add_neg]

theorem positiveWord_int (x : BitVec 32) :
    (positiveWord x).toInt = positive x.toInt := by
  rw [positiveWord_eq]
  have h := positive_bounds (BitVec.le_toInt x) (BitVec.toInt_lt (x := x))
  apply BitVec.toInt_ofInt_eq_self (by decide) <;> omega

theorem positiveWord_nat (x : BitVec 32) :
    (positiveWord x).toNat = (positive x.toInt).toNat := by
  have h := positive_bounds (BitVec.le_toInt x) (BitVec.toInt_lt (x := x))
  have he := positiveWord_int x
  have ht := BitVec.toInt_eq_toNat_cond (positiveWord x)
  split at ht <;> omega

theorem reciprocal_word_int {z : Int} (hz : 0 ≤ z) (hz' : z < 8380417) :
    (BitVec.ofInt 32 (reciprocal z)).toInt = reciprocal z := by
  have h := reciprocal_bounds hz hz'
  apply BitVec.toInt_ofInt_eq_self (by decide) <;> omega

/-- SQDMULH cannot saturate for an exact nonnegative twiddle reciprocal. -/
theorem sqdmulh_reciprocal (x : BitVec 32) {z : Int} (hz : 0 ≤ z) (hz' : z < 8380417) :
    sqdmulhLane x (BitVec.ofInt 32 (reciprocal z)) =
      some (BitVec.ofInt 32 (x.toInt * reciprocal z / 2147483648)) := by
  have hr := reciprocal_bounds hz hz'
  have hi := reciprocal_word_int hz hz'
  have hn : BitVec.ofInt 32 (reciprocal z) ≠ 0x80000000#32 := by
    intro h
    have he := congrArg BitVec.toInt h
    rw [hi] at he
    change reciprocal z = -2147483648 at he
    omega
  simp only [sqdmulhLane, hn, and_false, ite_false]
  rw [hi, Int.shiftRight_eq_div_pow]
  congr 2
  change 2 * x.toInt * reciprocal z / 4294967296 = x.toInt * reciprocal z / 2147483648
  have he : 2 * x.toInt * reciprocal z = 2 * (x.toInt * reciprocal z) := Int.mul_assoc _ _ _
  rw [he]
  omega

/-- Low-word MUL and MLS after SQDMULH; intermediate products may wrap. -/
def fastMulWord (x : BitVec 32) (z : Int) : BitVec 32 :=
  x * BitVec.ofInt 32 z -
    BitVec.ofInt 32 (x.toInt * reciprocal z / 2147483648) * BitVec.ofNat 32 q

theorem fastMulWord_eq (x : BitVec 32) (z : Int) :
    fastMulWord x z = BitVec.ofInt 32 (fastMul x.toInt z) := by
  unfold fastMulWord fastMul
  rw [Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg,
    BitVec.ofInt_mul, BitVec.ofInt_mul, BitVec.ofInt_toInt]
  change x * BitVec.ofInt 32 z -
      BitVec.ofInt 32 (x.toInt * reciprocal z / 2147483648) * 8380417#32 = _
  rw [BitVec.sub_eq_add_neg]
  rfl

theorem fastMulWord_int (x : BitVec 32) (z : Int) :
    (fastMulWord x z).toInt = fastMul x.toInt z := by
  rw [fastMulWord_eq]
  have h := fastMul_bounds (z := z) (BitVec.le_toInt x) (BitVec.toInt_lt (x := x))
  apply BitVec.toInt_ofInt_eq_self (by decide) <;> omega

/-- The existing exact seven-instruction REDC is valid when both factors are
positive lazy, rather than requiring a canonical twiddle. -/
theorem lazy_mont_word_nat (x z : BitVec 32)
    (hx : x.toNat < 3 * q) (hz : z.toNat < 3 * q) :
    (redc (product x z)).toNat = mont (x.toNat * z.toNat) := by
  rw [redc_nat _ (by rw [product_nat]; exact product_lt_qR hx hz), product_nat]

end VG.Proof.MlDsa.AArch64.Optimized
