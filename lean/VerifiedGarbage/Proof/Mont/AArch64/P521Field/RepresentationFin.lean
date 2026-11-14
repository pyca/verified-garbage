module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.RepresentationMath
public import VerifiedGarbage.Proof.Weierstrass.Env
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Product

/-! The cyclic conversions preserve the existing Montgomery call contracts. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square VG.Proof.Weierstrass

instance p521_field_neZero : NeZero fieldPrime := ⟨by
  dsimp only [fieldPrime]
  rw [prime_value]
  decide⟩

theorem p521_mont_unit : UnitMod fieldPrime montBase := by
  apply unitMod_pow_two
  dsimp only [fieldPrime]
  rw [prime_value]

theorem toMontValue_field {t : Nat} (ht : t<fieldPrime) :
    toM fieldPrime montBase (toMontValue t)=Fin.ofNat fieldPrime t := by
  rw [toMontValue_mod ht]
  exact toM_mont p521_mont_unit

theorem fromMontValue_field {t : Nat} (ht : t<fieldPrime) :
    Fin.ofNat fieldPrime (fromMontValue t)=toM fieldPrime montBase t := by
  apply toM_one_mul p521_mont_unit
  rw [Nat.mul_one,Nat.mod_eq_of_lt ht]
  exact fromMontValue_mod ht

/-- A verified Montgomery operation can be called between the two rotations
without changing its field-level result or strengthening its contract. -/
theorem ordinary_mont_call (f : Fin fieldPrime → Fin fieldPrime) {a r : Nat}
    (ha : a<fieldPrime) (hr : r<fieldPrime)
    (call : toM fieldPrime montBase r=f (toM fieldPrime montBase (toMontValue a))) :
    Fin.ofNat fieldPrime (fromMontValue r)=f (Fin.ofNat fieldPrime a) := by
  rw [fromMontValue_field hr,call,toMontValue_field ha]

end VG.Proof.Mont.AArch64.P521Field
