module

public import VerifiedGarbage.Spec.Dsa.Prevalidated
public import VerifiedGarbage.Proof.Dsa.Accepted
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Dsa.Encoding

/-! # Public-key validation, on any target

`validatePublicKeyBytes_eq`: the specification's validation of a packed
public key is the shape of its domain (`shapeValid`) and the algebraic
checks of its public part (`publicChecks`), which the implementations
evaluate. `validKeyWitness` is a packed key that passes validation, for the
satisfiability of contracts that ask for one.
-/

@[expose] public section

namespace VG.Proof.Dsa

open VG

theorem validatePublicKeyBytes_eq {pLen qLen p q g y : Nat} {key : List Byte}
    (widths : Spec.Dsa.lengthsValid pLen qLen) (keyLen : key.length = 3 * pLen + qLen)
    (keyValue : Spec.Dsa.publicKeyBytes pLen qLen key = ⟨⟨p, q, g⟩, y, none⟩) :
    Spec.Dsa.validatePublicKeyBytes pLen qLen key = decide (shapeValid p q ∧ publicChecks p q g y) := by
  unfold Spec.Dsa.validatePublicKeyBytes
  simp only [widths, decide_true, Bool.not_true, keyLen, bne_self_eq_false, Bool.or_false,
    Bool.false_eq_true, ↓reduceIte, keyValue]
  by_cases hs : shapeValid p q
  · have e := publicChecks_spec (g := g) (y := y) hs
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_eq, hs, true_and, e]
  · have hp : ¬ Spec.Dsa.parametersValid ⟨p, q, g⟩ := fun P => hs (parametersValid_shape P)
    simp only [hp, hs, decide_false, Bool.false_and, false_and]

/-- A 1024/160 key that passes validation: with q = 3 (2^158 + 1) and
a = q 2^352, p = a² + a + 1 and g = y = a. Then q divides p − 1 and
a³ ≡ 1 (mod p). It is algebraically consistent, not a cryptographic domain
(validation does not test primality), and no test vector. -/
def validKeyWitness : List Byte :=
  let q := 3 * (2 ^ 158 + 1)
  let a := q * 2 ^ 352
  Spec.Dsa.encodeBE 128 (a * a + a + 1) ++ Spec.Dsa.encodeBE 20 q ++
    Spec.Dsa.encodeBE 128 a ++ Spec.Dsa.encodeBE 128 a

theorem validKeyWitness_length : validKeyWitness.length = 404 := by
  simp only [validKeyWitness, List.length_append, encodeBE_length]

theorem validKeyWitness_valid : Spec.Dsa.validatePublicKeyBytes 128 20 validKeyWitness = true := by
  decide +kernel

end VG.Proof.Dsa
