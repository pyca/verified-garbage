module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.BrainpoolP256r1Sha256
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Deterministic ECDSA (RFC 6979) over brainpoolP256r1 with HMAC-SHA-256 on PPC64LE -/

@[expose] public section

namespace VG.Generic.BrainpoolP256r1.PPC64LE.EcdsaBrainpoolP256r1Sha256

open VG.Proof.Ecdsa.Rfc6979.PPC64LE (sha256K)
open VG.Proof.Ecdsa.Rfc6979.PPC64LE.BrainpoolP256r1Sha256 (pack sign_verified)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP256r1.curve) : List Artifact := [
  Spec.Ecdsa.Rfc6979.BrainpoolP256r1Sha256.signApi.artifact PPC64LE.target {
    code := (pack h.law).c.sign
    stack := 400
    verified := sign_verified h.law }]

end VG.Generic.BrainpoolP256r1.PPC64LE.EcdsaBrainpoolP256r1Sha256
