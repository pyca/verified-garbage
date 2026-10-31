module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.BrainpoolP384r1Sha384
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Deterministic ECDSA (RFC 6979) over brainpoolP384r1 with HMAC-SHA-384 on x86 (32-bit) -/

@[expose] public section

namespace VG.Generic.BrainpoolP384r1.X86.EcdsaBrainpoolP384r1Sha384

open VG.Proof.Ecdsa.Rfc6979.X86 (cfgOf sign_spSafe)
open VG.Proof.Ecdsa.Rfc6979.X86.BrainpoolP384r1Sha384 (pack sign_verified)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP384r1.curve) : List Artifact := [
  Spec.Ecdsa.Rfc6979.BrainpoolP384r1Sha384.signApi.artifact X86.target {
    code := (cfgOf (pack h.law)).sign
    stack := 272
    verified := sign_verified h.law
    spSafe := sign_spSafe (pack h.law) }]

end VG.Generic.BrainpoolP384r1.X86.EcdsaBrainpoolP384r1Sha384
