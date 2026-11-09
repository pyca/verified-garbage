module

public import VerifiedGarbage.Proof.Dsa.Validation
public import VerifiedGarbage.Spec.Dsa.PrevalidatedSign
import VerifiedGarbage.Proof.Dsa.Encoding

/-! # Private-key validation, on any target

`validatePrivateKeyBytes_eq`: the specification's validation of a packed
private key is the shape of its domain and the algebraic checks of its
public and private parts, which the implementations evaluate.
`validPrivateKeyWitness` is a packed private key that passes validation,
for the satisfiability of contracts that ask for one. -/

@[expose] public section

namespace VG.Proof.Dsa

theorem validatePrivateKeyBytes_eq {pLen qLen p q g y x : Nat} {key : List Byte}
    (widths : Spec.Dsa.lengthsValid pLen qLen) (keyLen : key.length = 3 * pLen + 2 * qLen)
    (keyValue : Spec.Dsa.privateKeyBytes pLen qLen key = ⟨⟨p, q, g⟩, y, some x⟩) :
    Spec.Dsa.validatePrivateKeyBytes pLen qLen key =
      decide (shapeValid p q ∧ publicChecks p q g y ∧ (0 < x ∧ x < q) ∧ g ^ x % p = y) := by
  unfold Spec.Dsa.validatePrivateKeyBytes
  simp only [widths, decide_true, Bool.not_true, keyLen, bne_self_eq_false, Bool.or_false,
    Bool.false_eq_true, ↓reduceIte, keyValue]
  by_cases hs : shapeValid p q
  · have e := privateChecks_spec (g := g) (y := y) (x := x) hs
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_eq, hs, true_and, e]
  · have hp : ¬ Spec.Dsa.parametersValid ⟨p, q, g⟩ := fun P => hs (parametersValid_shape P)
    simp only [hp, hs, decide_false, Bool.false_and, false_and]

/-- `validKeyWitness` with the private scalar 1: its g and y are equal. -/
def validPrivateKeyWitness : List Byte := validKeyWitness ++ Spec.Dsa.encodeBE 20 1

theorem validPrivateKeyWitness_length : validPrivateKeyWitness.length = 424 := by
  simp only [validPrivateKeyWitness, List.length_append, validKeyWitness_length, encodeBE_length]

theorem validPrivateKeyWitness_valid :
    Spec.Dsa.validatePrivateKeyBytes 128 20 validPrivateKeyWitness = true := by
  decide +kernel

end VG.Proof.Dsa
