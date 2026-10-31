module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.BrainpoolP512r1Sha512
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Deterministic ECDSA (RFC 6979) over brainpoolP512r1 with HMAC-SHA-512 on x86 (32-bit) -/

@[expose] public section

namespace VG.Generic.BrainpoolP512r1.X86.EcdsaBrainpoolP512r1Sha512

open VG.Proof.Ecdsa.Rfc6979.X86 (cfgOf sign_spSafe)
open VG.Proof.Ecdsa.Rfc6979.X86.BrainpoolP512r1Sha512 (pack sign_verified)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP512r1.curve) : List Artifact := [
  Spec.Ecdsa.Rfc6979.BrainpoolP512r1Sha512.signApi.artifact X86.target {
    code := (cfgOf (pack h.law)).sign
    stack := 336
    verified := sign_verified h.law
    spSafe := sign_spSafe (pack h.law) }]

end VG.Generic.BrainpoolP512r1.X86.EcdsaBrainpoolP512r1Sha512
