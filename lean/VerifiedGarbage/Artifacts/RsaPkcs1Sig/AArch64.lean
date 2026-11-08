module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.SignVerified
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callees
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.SignPre
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.SignCT
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.VerifyFrame
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.AArch64
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.PrecomputedVerified
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.RecPcVerified
public import VerifiedGarbage.Impl.RsaPkcs1Sig.AArch64.RecoverPrecomputed
public import VerifiedGarbage.Impl.RsaPkcs1Sig.AArch64.Precomputed
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.VerifyPre
public import VerifiedGarbage.Spec.RsaPkcs1Sig.Precomputed
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.RecPcCorrect
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.RecPcTail
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Recover
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Verify
public import VerifiedGarbage.Proof.Variants.RsaPublicPrecomputed.AArch64

/-! # RSASSA-PKCS1-v1_5 signing on AArch64, for each implementation of the CRT -/

@[expose] public section

namespace VG.Artifacts.RsaPkcs1Sig.AArch64.RsaPrivateCrt

open VG.Proof.Rsa.AArch64 (CrtImpl)
open VG.Proof.RsaPkcs1Sig.AArch64

def artifacts (v : CrtImpl) : List Artifact := [
  Spec.RsaPkcs1Sig.signApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.RsaPkcs1Sig.AArch64.Sign.code (privOf v).name (privOf v).code
    stack := Sgn.stk (privOf v).stack
    verified := Sgn.code_verified (privOf v)
    features := v.features }]

end VG.Artifacts.RsaPkcs1Sig.AArch64.RsaPrivateCrt

-- PKCS #1 v1.5 verification and recovery over precomputed RSA public variants on AArch64
namespace VG.Artifacts.RsaPkcs1Sig.AArch64.RsaPublicPrecomputed

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

end VG.Artifacts.RsaPkcs1Sig.AArch64.RsaPublicPrecomputed

namespace VG.Artifacts.RsaPkcs1Sig.AArch64

def artifacts : List Artifact :=
  (VG.Proof.Variants.RsaPrivateCrt.AArch64.variants.flatMap fun v => RsaPrivateCrt.artifacts v) ++
  (VG.Proof.Variants.RsaPublicPrecomputed.AArch64.variants.flatMap fun v => RsaPublicPrecomputed.artifacts v)

end VG.Artifacts.RsaPkcs1Sig.AArch64
