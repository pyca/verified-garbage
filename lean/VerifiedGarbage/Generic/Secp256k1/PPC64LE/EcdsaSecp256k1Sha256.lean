module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Secp256k1Sha256
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Deterministic ECDSA (RFC 6979) over secp256k1 with HMAC-SHA-256 on PPC64LE -/

@[expose] public section

namespace VG.Generic.Secp256k1.PPC64LE.EcdsaSecp256k1Sha256

open VG.Proof.Ecdsa.Rfc6979.PPC64LE (sha256K)
open VG.Proof.Ecdsa.Rfc6979.PPC64LE.Secp256k1Sha256 (pack sign_verified)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.Secp256k1.curve) : List Artifact := [
  Spec.Ecdsa.Rfc6979.Secp256k1Sha256.signApi.artifact PPC64LE.target {
    code := (pack h.law).c.sign
    stack := 400
    verified := sign_verified h.law }]

end VG.Generic.Secp256k1.PPC64LE.EcdsaSecp256k1Sha256
