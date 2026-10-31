module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.BrainpoolP384r1Sha384
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Deterministic ECDSA (RFC 6979) over brainpoolP384r1 with HMAC-SHA-384 on PPC64LE -/

@[expose] public section

namespace VG.Generic.BrainpoolP384r1.PPC64LE.EcdsaBrainpoolP384r1Sha384

open VG.Proof.Ecdsa.Rfc6979.PPC64LE (sha384K)
open VG.Proof.Ecdsa.Rfc6979.PPC64LE.BrainpoolP384r1Sha384 (pack sign_verified)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP384r1.curve) : List Artifact := [
  Spec.Ecdsa.Rfc6979.BrainpoolP384r1Sha384.signApi.artifact PPC64LE.target {
    code := (pack h.law).c.sign
    stack := 400
    verified := sign_verified h.law }]

end VG.Generic.BrainpoolP384r1.PPC64LE.EcdsaBrainpoolP384r1Sha384
