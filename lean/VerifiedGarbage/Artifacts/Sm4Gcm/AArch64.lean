module

public import VerifiedGarbage.Proof.Sm4.AArch64.Ctr32Verified
public import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Frame
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.Proof.Sm4.AArch64.Ctr32Lit
public import VerifiedGarbage.Proof.AesGcm.AArch64.Frame
public import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Instances
public import VerifiedGarbage.Proof.AesGcm.AArch64.GhashImpls
public import VerifiedGarbage.Proof.Variants.Sm4Gcm.AArch64

/-! # SM4-GCM on baseline AArch64: its key setup -/

@[expose] public section

namespace VG.Artifacts.Sm4Gcm.AArch64

def direct : List Artifact := [
  Spec.Sm4.Gcm.initApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratch 768 .x2 Impl.Sm4Gcm.AArch64.init
    stack := 4032
    verified := Proof.Sm4Gcm.AArch64.init_framed }]

end VG.Artifacts.Sm4Gcm.AArch64

-- SM4-GCM (NIST SP 800-38D with SM4, RFC 8998) on AArch64
namespace VG.Artifacts.Sm4Gcm.AArch64.Sm4Gcm

open VG.Proof.Sm4Gcm.AArch64

/-- The artifacts calling the implementations `v`. -/
def artifactsOf (v : GcmImpl) : List Artifact := [
  Spec.Sm4.Gcm.sealApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.StackScratch.AArch64.withStackArgScratch 784 0 (Impl.Sm4Gcm.AArch64.«seal» v.callees)
    stack := 4048
    verified := seal_framed v
    features := v.features },
  Spec.Sm4.Gcm.openApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.StackScratch.AArch64.withStackArgScratch 784 1 (Impl.Sm4Gcm.AArch64.«open» v.callees)
    stack := 4048
    verified := open_framed v
    features := v.features },
  Spec.Sm4.Gcm.streamEncryptApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.StackScratch.AArch64.withStackScratch 768 .x6
      (Impl.Sm4Gcm.AArch64.streamEncrypt v.callees)
    stack := 4032
    verified := streamEncrypt_framed v
    features := v.features },
  Spec.Sm4.Gcm.streamDecryptApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.StackScratch.AArch64.withStackScratch 768 .x6
      (Impl.Sm4Gcm.AArch64.streamDecrypt v.callees)
    stack := 4032
    verified := streamDecrypt_framed v
    features := v.features },
  Spec.Sm4.Gcm.streamFinishApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.StackScratch.AArch64.withStackScratch 768 .x5
      (Impl.Sm4Gcm.AArch64.streamFinish v.callees)
    stack := 4032
    verified := streamFinish_framed v
    features := v.features },
  Spec.Sm4.Gcm.streamVerifyApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.StackScratch.AArch64.withStackScratch 768 .x6
      (Impl.Sm4Gcm.AArch64.streamVerify v.callees)
    stack := 4032
    verified := streamVerify_framed v
    features := v.features }]

/-- `vg_sm4_gcm_stream_init` and `vg_sm4_gcm_stream_aad`: AES-GCM's code and
proofs, calling the implementation of `vg_ghash` the variant `v` names (and no
cipher). -/
def artifactsAes (v : GcmVariant) : List Artifact := [
  Spec.Sm4.Gcm.streamInitApi.artifact AArch64.target {
    suffix := v.gh.impl.suffix
    code := Impl.StackScratch.AArch64.withStackScratch 2560 .x4
      (Impl.AesGcm.AArch64.streamInit (Proof.AesGcm.AArch64.GcmVariant.impl ⟨.scalar, .scalar, v.gh, false⟩).callees)
    stack := 2560
    verified := Proof.AesGcm.AArch64.streamInit_framed
      (Proof.AesGcm.AArch64.GcmVariant.impl ⟨.scalar, .scalar, v.gh, false⟩)
    features := v.gh.impl.features },
  Spec.Sm4.Gcm.streamAadApi.artifact AArch64.target {
    suffix := v.gh.impl.suffix
    code := Impl.StackScratch.AArch64.withStackScratch 2560 .x5
      (Impl.AesGcm.AArch64.streamAad (Proof.AesGcm.AArch64.GcmVariant.impl ⟨.scalar, .scalar, v.gh, false⟩).callees)
    stack := 2560
    verified := Proof.AesGcm.AArch64.streamAad_framed
      (Proof.AesGcm.AArch64.GcmVariant.impl ⟨.scalar, .scalar, v.gh, false⟩)
    features := v.gh.impl.features }]

/-- The artifacts calling the implementation of `vg_ghash` the variant `v` names. -/
def artifacts (v : GcmVariant) : List Artifact := artifactsOf ⟨v.gh.impl⟩ ++ artifactsAes v

end VG.Artifacts.Sm4Gcm.AArch64.Sm4Gcm

namespace VG.Artifacts.Sm4Gcm.AArch64

def artifacts : List Artifact :=
  direct ++
  (VG.Proof.Variants.Sm4Gcm.AArch64.variants.flatMap fun v => Sm4Gcm.artifacts v)

end VG.Artifacts.Sm4Gcm.AArch64
