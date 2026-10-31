module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.P521Sha512
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Deterministic ECDSA (RFC 6979) over P-521 with HMAC-SHA-512 on x86 (32-bit) -/

@[expose] public section

namespace VG.Generic.P521.X86.EcdsaP521Sha512

open VG.Proof.Ecdsa.Rfc6979.X86 (cfgOf sign_spSafe)
open VG.Proof.Ecdsa.Rfc6979.X86.P521Sha512 (pack sign_verified)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P521.curve) : List Artifact := [
  Spec.Ecdsa.Rfc6979.P521Sha512.signApi.artifact X86.target {
    code := (cfgOf (pack h.law)).sign
    stack := 416
    verified := sign_verified h.law
    spSafe := sign_spSafe (pack h.law) }]

end VG.Generic.P521.X86.EcdsaP521Sha512
