module

import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.PcVerified
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callees
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Impl.RsaPkcs1Enc.AArch64.Precomputed
public import VerifiedGarbage.Spec.RsaPkcs1Enc.Precomputed
public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.PcVerified
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.Bytes
public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncCorrect
public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncVerified
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.Bytes
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncCorrect
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncVerified

/-! # PKCS #1 v1.5 encryption over precomputed RSA public variants on AArch64 -/

@[expose] public section

namespace VG.Generic.RsaPublicPrecomputed.AArch64.RsaPkcs1Enc

open VG.Proof.Rsa.AArch64 (PublicImpl)
open VG.Proof.RsaPkcs1Sig.AArch64 (pdOf)
open VG.Proof.RsaPkcs1Enc.AArch64.Enc

def artifacts (v : PublicImpl) : List Artifact := [
  Spec.RsaPkcs1Enc.encryptPrecomputedApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.RsaPkcs1Enc.AArch64.Precomputed.code (pdOf v).name (pdOf v).code
    stack := (pdOf v).stack + 1088
    verified := Pc.code_verified (pdOf v) Pc.sat
    features := v.features }]

end VG.Generic.RsaPublicPrecomputed.AArch64.RsaPkcs1Enc
