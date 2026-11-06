module

public import VerifiedGarbage.Spec.RsaPss
public import VerifiedGarbage.Spec.RsaPss.Contract

/-!
# EMSA-PSS encoding and its check, as functions

Not trusted: the contracts of internal functions (`Rust.Internal`), which only
verified code calls, that their proofs and their callers' compose.

The two halves of RSASSA-PSS that
use the hash functions, `encode` (EMSA-PSS-ENCODE, RFC 8017 §9.1.1) and
`verifyEncoding` (EMSA-PSS-VERIFY, §9.1.2), as functions of their own, so
that signing and verification can call them around the RSA primitive.

A function that calls functions with variants has one copy for each of
their implementations it can reach: today every RSA-PSS function is
copied for each implementation of its hash function times each of the RSA
primitive's (on x86-64, base, `adx` and `ifma`). With these two functions,
only they depend on the hash function's implementation, and signing and
verification shrink to calls. The contracts of `sign` and `verify` are
unchanged: they still state the whole of RSASSA-PSS.

Both are constant time but for the lengths: the digest, the salt and the
encoding are secret (an encoding checked during verification is the RSA
result of a signature that may be chosen to probe it).
-/

@[expose] public section

namespace VG.Proof.RsaPss

open VG.Spec VG.Spec.RsaPss
open VG.Spec.Mgf1 (Hash)
open VG.Spec.Rsa (bytesAt)

variable (H G : Hash)

/-- The 64-bit words of working space the encoding functions use. -/
def encodingScratchWords : Nat := 1024

/-- The most bits of an encoding: that of a modulus of 8192 bits. -/
def maxEmBits : Nat := 8191



end VG.Proof.RsaPss
