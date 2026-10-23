module

public import VerifiedGarbage.Spec.Dsa.Prevalidated
import VerifiedGarbage.Proof.Dsa.Encoding

/-! # An explicit algebraically consistent domain witnesses the validated precondition

The contract checks algebraic consistency rather than primality. Let a=q·2^352,
q=3·(2^158+1), p=a²+a+1 and g=y=a. Then q divides p−1 and g³=1 mod p.
This is a satisfiability witness, not a cryptographic domain or a test vector.
-/

@[expose] public section
namespace VG.Proof.Dsa.AArch64

def validatedSatKey : List Byte :=
  let q := 3 * (2 ^ 158 + 1)
  let a := q * 2 ^ 352
  Spec.Dsa.encodeBE 128 (a * a + a + 1) ++ Spec.Dsa.encodeBE 20 q ++
    Spec.Dsa.encodeBE 128 a ++ Spec.Dsa.encodeBE 128 a

theorem validatedSatKey_length : validatedSatKey.length = 404 := by
  simp only [validatedSatKey, List.length_append, VG.Proof.Dsa.encodeBE_length]

theorem validatedSatKey_valid : Spec.Dsa.validatePublicKeyBytes 128 20 validatedSatKey = true := by
  decide +kernel

end VG.Proof.Dsa.AArch64
