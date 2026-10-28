module
public import VerifiedGarbage.Proof.Rsa.X86.BatchLaw
import VerifiedGarbage.Proof.Rsa.X86.GcdBatch.BodyProof
/-! # Closed arithmetic proofs supplied at RSA registration -/
@[expose] public section
namespace VG.Proof.Rsa.X86
instance batchLaw : BatchLaw where
  gcd_ok := GcdBatch.body_ok_proof
end VG.Proof.Rsa.X86
