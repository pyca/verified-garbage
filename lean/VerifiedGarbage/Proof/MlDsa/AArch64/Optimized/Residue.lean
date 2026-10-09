import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Arithmetic
import VerifiedGarbage.Proof.MlDsa.KeyGen.Poly

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.KeyGen (ofInt_val)

theorem ofInt_add (a b : Int) : ofInt (a + b) = ofInt a + ofInt b := by
  apply Fin.ext
  apply Int.ofNat_inj.mp
  rw [ofInt_val, val_add', Int.natCast_emod, Int.natCast_add, ofInt_val, ofInt_val]
  change (a + b) % 8380417 = (a % 8380417 + b % 8380417) % 8380417
  exact Int.add_emod _ _ _

theorem ofInt_mul (a b : Int) : ofInt (a * b) = ofInt a * ofInt b := by
  apply Fin.ext
  apply Int.ofNat_inj.mp
  rw [ofInt_val, val_mul, Int.natCast_emod, Int.natCast_mul, ofInt_val, ofInt_val]
  change (a * b) % 8380417 = (a % 8380417 * (b % 8380417)) % 8380417
  exact Int.mul_emod _ _ _

theorem ofInt_sub (a b : Int) : ofInt (a - b) = ofInt a - ofInt b := by
  apply Fin.ext
  apply Int.ofNat_inj.mp
  rw [ofInt_val, val_sub', Int.natCast_emod, Int.natCast_add,
    Int.natCast_sub (Nat.le_of_lt (ofInt b).isLt), ofInt_val, ofInt_val]
  change (a - b) % 8380417 = (a % 8380417 + (8380417 - b % 8380417)) % 8380417
  omega

theorem positive_field (x : Int) : ofInt (positive x) = ofInt x := by
  apply Fin.ext
  apply Int.ofNat_inj.mp
  rw [ofInt_val, ofInt_val, positive_mod]

theorem fastMul_field (x z : Int) : ofInt (fastMul x z) = ofInt x * ofInt z := by
  rw [← ofInt_mul]
  apply Fin.ext
  apply Int.ofNat_inj.mp
  rw [ofInt_val, ofInt_val, fastMul_mod]

end VG.Proof.MlDsa.AArch64.Optimized
