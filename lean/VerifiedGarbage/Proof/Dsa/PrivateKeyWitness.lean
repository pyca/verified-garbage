module

public import VerifiedGarbage.Proof.Dsa.Validation
public import VerifiedGarbage.Spec.Dsa.PrevalidatedSign
import VerifiedGarbage.Proof.Dsa.Encoding

/-! # A packed private key that passes validation, on any target

`validPrivateKeyWitness`, for the satisfiability of contracts that ask for
a validated private key. -/

@[expose] public section

namespace VG.Proof.Dsa

/-- `validKeyWitness` with the private scalar 1: its g and y are equal. -/
def validPrivateKeyWitness : List Byte := validKeyWitness ++ Spec.Dsa.encodeBE 20 1

theorem validPrivateKeyWitness_length : validPrivateKeyWitness.length = 424 := by
  simp only [validPrivateKeyWitness, List.length_append, validKeyWitness_length, encodeBE_length]

theorem validPrivateKeyWitness_valid :
    Spec.Dsa.validatePrivateKeyBytes 128 20 validPrivateKeyWitness = true := by
  decide +kernel

end VG.Proof.Dsa
