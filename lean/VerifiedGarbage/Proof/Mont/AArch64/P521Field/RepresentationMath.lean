module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Rotate
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionMath
import VerifiedGarbage.Proof.Framework.Omega

/-! Canonical conversions between ordinary P-521 residues and Montgomery form. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square

def fromMontValue (t : Nat) : Nat := t/rotateBase+upperBase*(t%rotateBase)
def toMontValue (t : Nat) : Nat := rotateBase*(t%upperBase)+t/upperBase

theorem fromMontValue_bound {t : Nat} (ht : t<fieldPrime) : fromMontValue t<fieldPrime :=
  (rotation_mod ht).1

theorem fromMontValue_mod {t : Nat} (ht : t<fieldPrime) :
    fromMontValue t*montBase%fieldPrime=t := (rotation_mod ht).2

theorem toMontValue_bound {t : Nat} (ht : t<fieldPrime) : toMontValue t<fieldPrime := by
  have hpos : 0<upperBase := by apply Nat.pow_pos; decide
  have hrem := Nat.mod_lt t hpos
  have hdiv := Nat.mod_add_div t upperBase
  dsimp only [toMontValue,fieldPrime,rotateBase,upperBase] at *
  omega

theorem fromMont_toMont {t : Nat} (ht : t<fieldPrime) : fromMontValue (toMontValue t)=t := by
  have h := Nat.mod_add_div t upperBase
  have hpos : 0<upperBase := by apply Nat.pow_pos; decide
  have hrem := Nat.mod_lt t hpos
  have hq : t/upperBase<rotateBase := by
    dsimp only [fieldPrime,upperBase,rotateBase] at *
    omega
  dsimp only [fromMontValue,toMontValue]
  have hm : (rotateBase*(t%upperBase)+t/upperBase)%rotateBase=t/upperBase := by
    rw [Nat.mul_add_mod,Nat.mod_eq_of_lt hq]
  have hd : (rotateBase*(t%upperBase)+t/upperBase)/rotateBase=t%upperBase := by
    dsimp only [rotateBase] at hq ⊢
    omega
  rw [hm,hd]
  omega

theorem toMontValue_mod {t : Nat} (ht : t<fieldPrime) :
    toMontValue t=t*montBase%fieldPrime := by
  have h := fromMontValue_mod (toMontValue_bound ht)
  rw [fromMont_toMont ht] at h
  exact h.symm

theorem toMont_fromMont {t : Nat} (ht : t<fieldPrime) : toMontValue (fromMontValue t)=t := by
  rw [toMontValue_mod (fromMontValue_bound ht),fromMontValue_mod ht]

theorem fromMontValue_zero : fromMontValue 0=0 := by
  simp only [fromMontValue,Nat.zero_div,Nat.zero_mod,Nat.mul_zero,Nat.zero_add]

theorem toMontValue_zero : toMontValue 0=0 := by
  simp only [toMontValue,Nat.zero_div,Nat.zero_mod,Nat.mul_zero,Nat.zero_add]

theorem toMontValue_zero_iff {a : Nat} (bound : a<fieldPrime) : toMontValue a=0 ↔ a=0 := by
  constructor
  · intro h
    have same:=congrArg fromMontValue h
    rw [fromMont_toMont bound,fromMontValue_zero] at same
    exact same
  · rintro rfl
    exact toMontValue_zero

end VG.Proof.Mont.AArch64.P521Field
