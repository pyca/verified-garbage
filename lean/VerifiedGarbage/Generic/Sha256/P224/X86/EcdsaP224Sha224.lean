module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.P224Sha224
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Deterministic ECDSA (RFC 6979) over P-224 with HMAC-SHA-224 on x86, for every x86 SHA-256 backend -/

@[expose] public section

namespace VG.Generic.Sha256.P224.X86.EcdsaP224Sha224

open VG.Proof.Ecdsa.Rfc6979.X86 (cfgOf sign_spSafe)
open VG.Proof.Ecdsa.Rfc6979.X86.P224Sha224 (pack sign_verified)

def artifacts (v : Proof.Sha256.X86.Variants.Backend) (h : Proof.Weierstrass.HasLaw Spec.P224.curve) :
    List Artifact := [
  Spec.Ecdsa.Rfc6979.P224Sha224.signApi.artifact X86.target {
    suffix := v.suffix
    code := (cfgOf (pack h.law v)).sign
    stack := 272
    verified := sign_verified h.law v
    spSafe := sign_spSafe (pack h.law v)
    features := v.features }]

end VG.Generic.Sha256.P224.X86.EcdsaP224Sha224
