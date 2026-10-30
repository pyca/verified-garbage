module

public import VerifiedGarbage.Proof.Rsa.X86.BatchLaw

import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Body
import VerifiedGarbage.Proof.Rsa.X86.GcdBatchRt.Body
/-! # Closed arithmetic proofs supplied at RSA registration -/

@[expose] public section
namespace VG.Proof.Rsa.X86
instance batchLaw : BatchLaw where
  gcd_ok := GcdBatchRt.body_ok
  inv_ok := InvBatchRt.body_ok
end VG.Proof.Rsa.X86
