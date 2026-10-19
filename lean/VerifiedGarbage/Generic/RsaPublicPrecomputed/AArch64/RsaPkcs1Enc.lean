module

import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.PcVerified
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callees
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Impl.RsaPkcs1Enc.AArch64.Precomputed
public import VerifiedGarbage.Spec.RsaPkcs1Enc.Precomputed

/-! # PKCS #1 v1.5 encryption over precomputed RSA public variants on AArch64 -/

@[expose] public section

namespace VG.Generic.RsaPublicPrecomputed.AArch64.RsaPkcs1Enc

open VG.Proof.Rsa.AArch64 (PublicImpl)
open VG.Proof.RsaPkcs1Sig.AArch64 (pdOf)
open VG.Proof.RsaPkcs1Enc.AArch64.Enc

def artifacts (v : PublicImpl) : List Artifact := [
  Spec.RsaPkcs1Enc.encryptPrecomputedApi.artifact AArch64.target {
    suffix := v.suffix
    notes := ["This implementation builds \
      `EM = 0x00 ‖ 0x02 ‖ PS ‖ 0x00 ‖ M` in its frame, finding whether `PS` has a zero byte without a \
      branch, and calls `" ++ v.name ++ "` on it with the cached modulus values. It then sets `out` to \
      zeros and the result to 0 under a mask if `PS` had a zero byte, without branching on the public \
      operation's result, and overwrites the frame's `EM` with zeros either way."]
    code := Impl.RsaPkcs1Enc.AArch64.Precomputed.code (pdOf v).name (pdOf v).code
    stack := (pdOf v).stack + 1088
    verified := Pc.code_verified (pdOf v) Pc.sat
    features := v.features }]

end VG.Generic.RsaPublicPrecomputed.AArch64.RsaPkcs1Enc
