module

import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.SignVerified
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callees
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.SignPre

/-! # RSASSA-PKCS1-v1_5 signing on AArch64, for each implementation of the CRT -/

@[expose] public section

namespace VG.Generic.RsaPrivateCrt.AArch64.RsaPkcs1Sig

open VG.Proof.Rsa.AArch64 (CrtImpl)
open VG.Proof.RsaPkcs1Sig.AArch64

def artifacts (v : CrtImpl) : List Artifact := [
  Spec.RsaPkcs1Sig.signApi.artifact AArch64.target {
    suffix := v.suffix
    notes := ["This implementation writes EMSA-PKCS1-v1_5's \
      encoding of `digest` into its frame and signs it with `" ++ (privOf v).name ++ "`, which checks the \
      signature against `e`. Only the lengths, the hash function and the public key decide a branch or \
      an address."]
    code := Impl.RsaPkcs1Sig.AArch64.Sign.code (privOf v).name (privOf v).code
    stack := Sgn.stk (privOf v).stack
    verified := Sgn.code_verified (privOf v)
    features := v.features }]

end VG.Generic.RsaPrivateCrt.AArch64.RsaPkcs1Sig
