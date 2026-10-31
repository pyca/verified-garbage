module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.BrainpoolP512r1Sha512
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Deterministic ECDSA (RFC 6979) over brainpoolP512r1 with HMAC-SHA-512 on PPC64LE -/

@[expose] public section

namespace VG.Generic.BrainpoolP512r1.PPC64LE.EcdsaBrainpoolP512r1Sha512

open VG.Proof.Ecdsa.Rfc6979.PPC64LE (sha512K)
open VG.Proof.Ecdsa.Rfc6979.PPC64LE.BrainpoolP512r1Sha512 (pack sign_verified)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP512r1.curve) : List Artifact := [
  Spec.Ecdsa.Rfc6979.BrainpoolP512r1Sha512.signApi.artifact PPC64LE.target {
    code := (pack h.law).c.sign
    stack := 464
    verified := sign_verified h.law }]

end VG.Generic.BrainpoolP512r1.PPC64LE.EcdsaBrainpoolP512r1Sha512
