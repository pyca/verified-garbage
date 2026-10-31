module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.BrainpoolP256r1Sha256
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Deterministic ECDSA (RFC 6979) over brainpoolP256r1 with HMAC-SHA-256 on x86, for every x86 SHA-256 backend -/

@[expose] public section

namespace VG.Generic.Sha256.BrainpoolP256r1.X86.EcdsaBrainpoolP256r1Sha256

open VG.Proof.Ecdsa.Rfc6979.X86 (cfgOf sign_spSafe)
open VG.Proof.Ecdsa.Rfc6979.X86.BrainpoolP256r1Sha256 (pack sign_verified)

def artifacts (v : Proof.Sha256.X86.Variants.Backend) (h : Proof.Weierstrass.X86.Inv.HasLawInv Spec.BrainpoolP256r1.curve) :
    List Artifact := [
  Spec.Ecdsa.Rfc6979.BrainpoolP256r1Sha256.signApi.artifact X86.target {
    suffix := v.suffix
    code := (cfgOf (pack h.law h.inv v)).sign
    stack := 272
    verified := sign_verified h.law h.inv v
    spSafe := sign_spSafe (pack h.law h.inv v)
    features := v.features }]

end VG.Generic.Sha256.BrainpoolP256r1.X86.EcdsaBrainpoolP256r1Sha256
