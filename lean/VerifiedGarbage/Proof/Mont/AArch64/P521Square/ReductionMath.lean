module

public import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.PowLit

/-! Integer identities behind the P-521 fold, correction and Montgomery rotation. -/

@[expose] public section
set_option exponentiation.threshold 1024

namespace VG.Proof.Mont.AArch64.P521Square

abbrev fieldBase : Nat := 2^521
abbrev fieldPrime : Nat := 2^521-1
abbrev montBase : Nat := 2^576
abbrev rotateBase : Nat := 2^55
abbrev upperBase : Nat := 2^466

def canonicalFold (u : Nat) : Nat :=
 let s := u % fieldBase + u / fieldBase
 if fieldBase ≤ s+1 then s+1-fieldBase else s

/-- One Mersenne fold is below twice the prime for a reduced input's square. -/
theorem fold_sum_bound {u : Nat} (hu : u < fieldPrime*fieldPrime) :
    u % fieldBase + u / fieldBase < 2*fieldPrime := by
  have h := Nat.mod_lt u (by decide : 0<fieldBase)
  have hq : u/fieldBase < fieldPrime := by
    have he := Nat.mod_add_div u fieldBase
    dsimp only [fieldBase,fieldPrime] at *
    omega
  dsimp only [fieldBase,fieldPrime] at *
  omega

/-- Folding at bit 521 preserves the residue. -/
theorem fold_value_mod (u : Nat) :
    u % fieldPrime = (u % fieldBase + u / fieldBase) % fieldPrime := by
  let s := u % fieldBase + u / fieldBase
  have he : u = s + fieldPrime * (u/fieldBase) := by
    have h := Nat.mod_add_div u fieldBase
    dsimp only [s,fieldBase,fieldPrime] at *
    omega
  change u%fieldPrime=s%fieldPrime
  rw [he,Nat.add_mod,Nat.mul_mod,Nat.mod_self,Nat.zero_mul,Nat.zero_mod,Nat.add_zero,Nat.mod_mod]

/-- One subtraction suffices for the folded sum. -/
theorem canonical_sum {s : Nat} (hs : s<2*fieldPrime) :
    (if fieldBase≤s+1 then s+1-fieldBase else s)<fieldPrime ∧
    (if fieldBase≤s+1 then s+1-fieldBase else s)=s%fieldPrime := by
  by_cases h : fieldBase≤s+1
  · rw [ite_eq_left h]
    have hp : fieldPrime≤s := by dsimp only [fieldBase,fieldPrime] at *; omega
    have ht : s-fieldPrime<fieldPrime := by omega
    have he : s-fieldPrime=s+1-fieldBase := by dsimp only [fieldBase,fieldPrime] at *; omega
    have hm : s%fieldPrime=s-fieldPrime := (Nat.mod_eq_sub_mod hp).trans (Nat.mod_eq_of_lt ht)
    exact ⟨by rw [←he]; exact ht,he ▸ hm.symm⟩
  · rw [ite_eq_right h]
    have ht : s<fieldPrime := by dsimp only [fieldBase,fieldPrime] at *; omega
    exact ⟨ht,(Nat.mod_eq_of_lt ht).symm⟩

/-- The fold followed by one subtraction is the canonical residue. -/
theorem canonical_fold {u : Nat} (hu : u<fieldPrime*fieldPrime) :
    canonicalFold u<fieldPrime ∧ canonicalFold u=u%fieldPrime := by
  have h := canonical_sum (fold_sum_bound hu)
  exact ⟨h.1,h.2.trans (fold_value_mod u).symm⟩

/-- The carry and complement-subtraction implement the canonical fold.
`v` is the folded nine-word value and `w` the value before masking to 521 bits. -/
theorem carry_correction {s v w c b : Nat} (hs : s<2*fieldPrime)
    (hc : c≤1) (_hb : b≤1) (hv : v<montBase) (hw : w<montBase)
    (ev : v+montBase*c = s+1+montBase-fieldBase)
    (ew : w+1 = v+c+montBase*b) :
    w%fieldBase = (if fieldBase≤s+1 then s+1-fieldBase else s) ∧ w%fieldBase<fieldPrime := by
  have hcb : c=0 ∨ c=1 := by omega
  rcases hcb with rfl | rfl
  · have hs' : s+1<fieldBase := by dsimp only [fieldBase,montBase,fieldPrime] at *; omega
    have he : w = fieldBase*(2^55-1)+s := by dsimp only [fieldBase,montBase,fieldPrime] at *; omega
    have ht : s<fieldPrime := by dsimp only [fieldBase,fieldPrime] at *; omega
    have ht' : s<fieldBase := by dsimp only [fieldBase,fieldPrime] at *; omega
    rw [ite_eq_right (by omega),he,Nat.add_mod,Nat.mul_mod,Nat.mod_self,Nat.zero_mul,Nat.zero_mod,Nat.zero_add,Nat.mod_mod,Nat.mod_eq_of_lt ht']
    exact ⟨rfl,ht⟩
  · have hs' : fieldBase≤s+1 := by dsimp only [fieldBase,montBase,fieldPrime] at *; omega
    have he : w = s+1-fieldBase := by dsimp only [fieldBase,montBase,fieldPrime] at *; omega
    have ht : w<fieldPrime := by dsimp only [fieldBase,montBase,fieldPrime] at *; omega
    have ht' : w<fieldBase := by dsimp only [fieldBase,fieldPrime] at *; omega
    rw [Nat.mod_eq_of_lt ht',ite_eq_left hs']
    exact ⟨he,ht⟩

/-- Cyclic right rotation in 521 bits divides by `2^576` modulo the prime. -/
theorem rotation_mod {t : Nat} (ht : t<fieldPrime) :
    t/rotateBase+upperBase*(t%rotateBase) < fieldPrime ∧
    (t/rotateBase+upperBase*(t%rotateBase))*montBase%fieldPrime = t := by
  have hrem := Nat.mod_lt t (by decide : 0<rotateBase)
  have hdiv := Nat.mod_add_div t rotateBase
  have hsmall : t/rotateBase+upperBase*(t%rotateBase) < fieldPrime := by
    dsimp only [fieldPrime,rotateBase,upperBase] at *
    omega
  have hmul : (t/rotateBase+upperBase*(t%rotateBase))*rotateBase = t+fieldPrime*(t%rotateBase) := by
    dsimp only [fieldPrime,rotateBase,upperBase] at *
    omega
  have hR : montBase = rotateBase + fieldPrime*rotateBase := by decide
  refine ⟨hsmall,?_⟩
  rw [hR,Nat.mul_add,Nat.add_mod]
  have hz : (t/rotateBase+upperBase*(t%rotateBase))*(fieldPrime*rotateBase)%fieldPrime=0 := by
    simp only [Nat.mul_mod,Nat.mod_self,Nat.zero_mul,Nat.mul_zero,Nat.zero_mod]
  rw [hz,Nat.add_zero,Nat.mod_mod,hmul]
  simp only [Nat.add_mod,Nat.mul_mod,Nat.mod_self,Nat.zero_mul,Nat.zero_mod,Nat.add_zero,Nat.mod_mod]
  exact Nat.mod_eq_of_lt ht

end VG.Proof.Mont.AArch64.P521Square
