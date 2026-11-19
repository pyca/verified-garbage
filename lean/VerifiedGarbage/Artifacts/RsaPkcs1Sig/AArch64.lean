module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.SignVerified
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.SignPrecomputed
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callees
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
public import VerifiedGarbage.Proof.Rsa.AArch64.Scrub
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

/-! # RSASSA-PKCS1-v1_5 (RFC 8017) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.RsaPkcs1Sig.AArch64

open VG.Proof.Rsa.AArch64 (PublicImpl)

open VG.Proof.Rsa.AArch64 (CrtImpl)
open VG.Proof.RsaPkcs1Sig.AArch64

def artifacts : List Artifact :=
  (VG.Proof.Variants.RsaPrivateCrt.AArch64.variants.flatMap fun (v : CrtImpl) => [
    Spec.RsaPkcs1Sig.signPrecomputedApi.artifact AArch64.target (VG.AArch64.ScrubAll.withScrubAll {
      suffix := v.suffix
      code := Impl.RsaPkcs1Sig.AArch64.Sign.codeP (privPOf v).name (privPOf v).code
      verified := Sgn.signPrecomputed_verified (privPOf v) } (Proof.Rsa.AArch64.Scrub.pkcs1SignOk _))]) ++
  (VG.Proof.Variants.RsaPublicPrecomputed.AArch64.variants.attach.flatMap
      fun (v : { v : PublicImpl // v ∈ VG.Proof.Variants.RsaPublicPrecomputed.AArch64.variants }) => [
    Spec.RsaPkcs1Sig.verifyPrecomputedApi.artifact AArch64.target (VG.AArch64.ScrubAll.scrubAllOf {
      suffix := v.1.suffix
      code := Impl.RsaPkcs1Sig.AArch64.Precomputed.code (pdOf v.1).name (pdOf v.1).code
      verified := Pc.code_verified (pdOf v.1) } Scrub.publicClear (Proof.Rsa.AArch64.Scrub.pkcs1VerifyOk _)
      (Scrub.verifySide v.1 v.2)),
    Spec.RsaPkcs1Sig.recoverPrecomputedApi.artifact AArch64.target (VG.AArch64.ScrubAll.scrubAllOf {
      suffix := v.1.suffix
      code := Impl.RsaPkcs1Sig.AArch64.RecoverPrecomputed.code (pdOf v.1).name (pdOf v.1).code
      verified := RecPc.code_verified (pdOf v.1) } Scrub.publicClear (Proof.Rsa.AArch64.Scrub.pkcs1RecoverOk _)
      (Scrub.recoverSide v.1 v.2))])

end VG.Artifacts.RsaPkcs1Sig.AArch64
