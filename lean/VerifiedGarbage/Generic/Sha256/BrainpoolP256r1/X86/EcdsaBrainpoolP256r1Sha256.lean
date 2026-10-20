module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.BrainpoolP256r1Sha256
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# Deterministic ECDSA (RFC 6979) over brainpoolP256r1 with HMAC-SHA-256 on x86, for every x86 SHA-256 backend

`vg_ecdsa_brainpoolp256r1_sha256_sign`, calling HMAC-SHA-256's `init` and `finalize`
and SHA-256's streaming `update` made with the backend's compression
function, and `vg_ecdsa_brainpoolp256r1_sign`, is emitted for every backend, named with
its suffix (e.g. `vg_ecdsa_brainpoolp256r1_sha256_sign_shani`), and needs its CPU
features.

The stack is 272 bytes: a 196-byte frame, and the 76 bytes below it that the
calls use (up to 24 bytes of arguments and the return address, and 48 bytes
of stack for HMAC's functions).

It is generic over brainpoolP256r1's group law `h` too, the variant
`Variants/BrainpoolP256r1/X86/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.Sha256.BrainpoolP256r1.X86.EcdsaBrainpoolP256r1Sha256

open VG.Proof.Ecdsa.Rfc6979.X86 (cfgOf sign_spSafe signNotes)
open VG.Proof.Ecdsa.Rfc6979.X86.BrainpoolP256r1Sha256 (pack sign_verified)

def artifacts (v : Proof.Sha256.X86.Variants.Backend) (h : Proof.Weierstrass.X86.Inv.HasLawInv Spec.BrainpoolP256r1.curve) :
    List Artifact := [
  Spec.Ecdsa.Rfc6979.BrainpoolP256r1Sha256.signApi.artifact X86.target {
    suffix := v.suffix
    notes := [signNotes v.F.hiN v.F.H.updN v.F.hfN 32
      Spec.Ecdsa.BrainpoolP256r1.signApi.name]
    code := (cfgOf (pack h.law h.inv v)).sign
    stack := 272
    verified := sign_verified h.law h.inv v
    spSafe := sign_spSafe (pack h.law h.inv v)
    features := v.features }]

end VG.Generic.Sha256.BrainpoolP256r1.X86.EcdsaBrainpoolP256r1Sha256
