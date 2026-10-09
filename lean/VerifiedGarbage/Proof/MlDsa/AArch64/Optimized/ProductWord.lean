import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Word
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Residue

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith.Neon

/-- The signed representative consumed directly by the fused inverse. -/
def centeredProduct (x z : BitVec 32) : BitVec 32 :=
  redc (product x z) - BitVec.ofNat 32 q

theorem centeredWord_int (x : BitVec 32) (hx : x.toNat < 16760834) :
    (x - 8380417#32).toInt = (x.toNat : Int) - 8380417 := by
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_sub]
  have hq : (8380417#32).toNat = 8380417 := rfl
  rw [hq]
  split <;> omega

theorem centeredProduct_int (x z : BitVec 32)
    (hx : x.toNat < 3*q) (hz : z.toNat < 3*q) :
    (centeredProduct x z).toInt = (mont (x.toNat*z.toNat) : Int)-q := by
  have hn := lazy_mont_word_nat x z hx hz
  have hb := mont_lt (product_lt_qR hx hz)
  change (redc (product x z) - 8380417#32).toInt = _
  rw [centeredWord_int _ (by rw [hn]; exact hb), hn]
  rfl

theorem centeredProduct_bounds (x z : BitVec 32)
    (hx : x.toNat < 3*q) (hz : z.toNat < 3*q) :
    -(q : Int) ≤ (centeredProduct x z).toInt ∧ (centeredProduct x z).toInt ≤ 147168 := by
  rw [centeredProduct_int x z hx hz]
  exact mont_center_bounds (product_lt_nine_q2 hx hz)

/-- The inverse's final factor R cancels the product's Montgomery factor. -/
theorem centeredMont_scaled (t : Nat) :
    ofInt ((mont t : Int)-q) * ofInt 4294967296 = ofInt (t : Int) := by
  rw [← ofInt_mul]
  apply Fin.ext
  apply Int.ofNat_inj.mp
  rw [VG.Proof.MlDsa.KeyGen.ofInt_val, VG.Proof.MlDsa.KeyGen.ofInt_val]
  have he := congrArg (fun n : Nat => (n : Int)) (mont_mul t)
  have he' : (mont t : Int)*4294967296 = (t : Int)+(montM t : Int)*8380417 := by
    have hR : ((2^32 : Nat) : Int) = 4294967296 := by decide
    have hq : (q : Int) = 8380417 := by decide
    simpa only [Int.natCast_mul, Int.natCast_add, hR, hq] using he
  change (((mont t : Int)-8380417)*4294967296)%8380417 = (t : Int)%8380417
  rw [Int.sub_mul]
  omega

theorem centeredProduct_scaled (x z : BitVec 32)
    (hx : x.toNat < 3*q) (hz : z.toNat < 3*q) :
    ofInt (centeredProduct x z).toInt * ofInt 4294967296 =
      ofInt (x.toNat : Int) * ofInt (z.toNat : Int) := by
  rw [centeredProduct_int x z hx hz, centeredMont_scaled, ← ofInt_mul, Int.natCast_mul]

end VG.Proof.MlDsa.AArch64.Optimized
