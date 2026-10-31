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
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.PrecomputedVerified
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.RecPcVerified
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.RecPcCorrect
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.RecPcTail
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.RecoverVerified
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.VerifyVerified
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Recover
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Verify
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.RecPcCorrect
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.RecPcTail
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.RecoverVerified
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.VerifyVerified
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.RsaPkcs1Sig.Recover
import VerifiedGarbage.Proof.RsaPkcs1Sig.Verify

/-! # PKCS #1 v1.5 verification and recovery over precomputed RSA public variants on AArch64 -/

@[expose] public section

namespace VG.Generic.RsaPublicPrecomputed.AArch64.RsaPkcs1Sig

open VG.Proof.Rsa.AArch64 (PublicImpl)
open VG.Proof.RsaPkcs1Sig.AArch64

def artifacts (v : PublicImpl) : List Artifact := [
  Spec.RsaPkcs1Sig.verifyPrecomputedApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.RsaPkcs1Sig.AArch64.Precomputed.code (pdOf v).name (pdOf v).code
    stack := Ver.stk (pdOf v).stack
    verified := Pc.code_verified (pdOf v)
    features := v.features },
  Spec.RsaPkcs1Sig.recoverPrecomputedApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.RsaPkcs1Sig.AArch64.RecoverPrecomputed.code (pdOf v).name (pdOf v).code
    stack := Ver.stk (pdOf v).stack
    verified := RecPc.code_verified (pdOf v)
    features := v.features }]

end VG.Generic.RsaPublicPrecomputed.AArch64.RsaPkcs1Sig
