module
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.PlainSimp


/-! # Shared-width inverse arithmetic for ARMv7 register pairs -/

@[expose] public section

namespace VG.Proof.Bignum.Arm

/-- A Newton step computed on words is the step on integers, modulo `2⁶⁴`. -/
theorem newton64_val (a x : BitVec 64) :
    (((x * (BitVec.ofNat 64 2 - a * x)).toNat : Int) - x.toNat * (2 - a.toNat * x.toNat)) % 2 ^ 64 = 0 := by
  have hx := x.isLt; have ha := a.isLt
  have hR : (x * (BitVec.ofNat 64 2 - a * x)).toNat = x.toNat * (BitVec.ofNat 64 2 - a * x).toNat % 2 ^ 64 :=
    BitVec.toNat_mul _ _
  have hD : (BitVec.ofNat 64 2 - a * x).toNat = (2 ^ 64 - a.toNat * x.toNat % 2 ^ 64 + 2) % 2 ^ 64 := by
    rw [BitVec.toNat_sub, BitVec.toNat_mul, BitVec.toNat_ofNat]
  generalize (BitVec.ofNat 64 2 - a * x).toNat = D at hR hD
  generalize (x * (BitVec.ofNat 64 2 - a * x)).toNat = R at hR ⊢
  generalize x.toNat = X at *
  generalize a.toNat = A at *
  -- `D = 2 - A X + 2⁶⁴ j`.
  have hDj : (D : Int) = 2 - (A * X : Nat) + 2 ^ 64 * (((D : Int) - 2 + (A * X : Nat)) / 2 ^ 64) := by
    have : ((A * X : Nat) : Int) % 2 ^ 64 = ((A * X % 2 ^ 64 : Nat) : Int) := by omega
    omega
  generalize (((D : Int) - 2 + (A * X : Nat)) / 2 ^ 64) = j at hDj
  have hXD : ((X * D : Nat) : Int) = 2 * X - (X : Int) * (A * X : Nat) + 2 ^ 64 * (X * j) := by
    rw [Int.natCast_mul, hDj, Int.mul_add, Int.mul_sub, Int.mul_left_comm (X : Int) (2 ^ 64) j]
    omega
  have e : (X : Int) * (2 - (A : Int) * X) = 2 * X - (X : Int) * (A * X : Nat) := by
    rw [Int.mul_sub, Int.natCast_mul, Int.mul_comm (X : Int) 2]
  rw [e]
  have : ((X * D % 2 ^ 64 : Nat) : Int) = ((X * D : Nat) : Int) % 2 ^ 64 := by omega
  rw [hR, this, hXD]
  omega

end VG.Proof.Bignum.Arm
