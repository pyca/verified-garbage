module

import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.SignVerified
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callees
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.SignPre
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.SignVerified
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.SignCT
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.VerifyFrame
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.SignCT
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.VerifyFrame
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem

/-! # RSASSA-PKCS1-v1_5 signing on AArch64, for each implementation of the CRT -/

@[expose] public section

namespace VG.Generic.RsaPrivateCrt.AArch64.RsaPkcs1Sig

open VG.Proof.Rsa.AArch64 (CrtImpl)
open VG.Proof.RsaPkcs1Sig.AArch64

def artifacts (v : CrtImpl) : List Artifact := [
  Spec.RsaPkcs1Sig.signApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.RsaPkcs1Sig.AArch64.Sign.code (privOf v).name (privOf v).code
    stack := Sgn.stk (privOf v).stack
    verified := Sgn.code_verified (privOf v)
    features := v.features }]

end VG.Generic.RsaPrivateCrt.AArch64.RsaPkcs1Sig
