module

import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.PrecomputedVerified
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callees
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.RecPcVerified
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Impl.RsaPkcs1Sig.AArch64.RecoverPrecomputed
public import VerifiedGarbage.Impl.RsaPkcs1Sig.AArch64.Precomputed
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.VerifyPre
public import VerifiedGarbage.Spec.RsaPkcs1Sig.Precomputed

/-! # PKCS #1 v1.5 verification and recovery over precomputed RSA public variants on AArch64 -/

@[expose] public section

namespace VG.Generic.RsaPublicPrecomputed.AArch64.RsaPkcs1Sig

open VG.Proof.Rsa.AArch64 (PublicImpl)
open VG.Proof.RsaPkcs1Sig.AArch64

def artifacts (v : PublicImpl) : List Artifact := [
  Spec.RsaPkcs1Sig.verifyPrecomputedApi.artifact AArch64.target {
    suffix := v.suffix
    notes := ["This implementation calls `" ++ v.name ++
      "` with the cached modulus values, then compares the recovered encoding with EMSA-PKCS1-v1_5's \
      encoding of `digest`. It combines the padding result with the public operation's status without \
      branching on that status. It uses 2144 bytes of stack: its frame and 16 bytes below it for the \
      call."]
    code := Impl.RsaPkcs1Sig.AArch64.Precomputed.code (pdOf v).name (pdOf v).code
    stack := Ver.stk (pdOf v).stack
    verified := Pc.code_verified (pdOf v)
    features := v.features },
  Spec.RsaPkcs1Sig.recoverPrecomputedApi.artifact AArch64.target {
    suffix := v.suffix
    notes := ["This implementation calls `" ++ v.name ++
      "` with the cached modulus values into its frame, writes EMSA-PKCS1-v1_5's encoding of the last \
      `out_len` bytes of the result beside it and compares the two, then copies those bytes to `out` and \
      masks them to zeros, and the result to 0, unless the public operation succeeded and the two are \
      equal: nothing after the call branches on its result. It uses 2144 bytes of stack: its frame and 16 \
      bytes below it for the call."]
    code := Impl.RsaPkcs1Sig.AArch64.RecoverPrecomputed.code (pdOf v).name (pdOf v).code
    stack := Ver.stk (pdOf v).stack
    verified := RecPc.code_verified (pdOf v)
    features := v.features }]

end VG.Generic.RsaPublicPrecomputed.AArch64.RsaPkcs1Sig
