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

/-! # SM4-GCM (NIST SP 800-38D, RFC 8998) on AArch64 -/

@[expose] public section

-- SM4-GCM (NIST SP 800-38D with SM4, RFC 8998) on AArch64
namespace VG.Artifacts.Sm4Gcm.AArch64.Sm4Gcm

open VG.Proof.Sm4Gcm.AArch64

/-- The artifacts calling the implementations `v`. -/
def artifactsOf (v : GcmVariant) : List Artifact := [
  Spec.Sm4.Gcm.sealApi.artifact AArch64.target {
    suffix := (⟨v.gh.impl, v.ctr.impl⟩ : GcmImpl).suffix
    code := Impl.StackScratch.AArch64.withStackArgScratch 784 0 (Impl.Sm4Gcm.AArch64.«seal» (⟨v.gh.impl, v.ctr.impl⟩ : GcmImpl).callees)
    verified := .unscrubbed (seal_framed (⟨v.gh.impl, v.ctr.impl⟩ : GcmImpl) (CtrName.stack_cases v.ctr)) },
  Spec.Sm4.Gcm.openApi.artifact AArch64.target {
    suffix := (⟨v.gh.impl, v.ctr.impl⟩ : GcmImpl).suffix
    code := Impl.StackScratch.AArch64.withStackArgScratch 784 1 (Impl.Sm4Gcm.AArch64.«open» (⟨v.gh.impl, v.ctr.impl⟩ : GcmImpl).callees)
    verified := .unscrubbed (open_framed (⟨v.gh.impl, v.ctr.impl⟩ : GcmImpl) (CtrName.stack_cases v.ctr)) },
  Spec.Sm4.Gcm.streamEncryptApi.artifact AArch64.target {
    suffix := (⟨v.gh.impl, v.ctr.impl⟩ : GcmImpl).suffix
    code := Impl.StackScratch.AArch64.withStackScratch 768 .x6
      (Impl.Sm4Gcm.AArch64.streamEncrypt (⟨v.gh.impl, v.ctr.impl⟩ : GcmImpl).callees)
    verified := .unscrubbed (streamEncrypt_framed (⟨v.gh.impl, v.ctr.impl⟩ : GcmImpl) (CtrName.stack_cases v.ctr)) },
  Spec.Sm4.Gcm.streamDecryptApi.artifact AArch64.target {
    suffix := (⟨v.gh.impl, v.ctr.impl⟩ : GcmImpl).suffix
    code := Impl.StackScratch.AArch64.withStackScratch 768 .x6
      (Impl.Sm4Gcm.AArch64.streamDecrypt (⟨v.gh.impl, v.ctr.impl⟩ : GcmImpl).callees)
    verified := .unscrubbed (streamDecrypt_framed (⟨v.gh.impl, v.ctr.impl⟩ : GcmImpl) (CtrName.stack_cases v.ctr)) },
  Spec.Sm4.Gcm.streamFinishApi.artifact AArch64.target {
    suffix := (⟨v.gh.impl, v.ctr.impl⟩ : GcmImpl).suffix
    code := Impl.StackScratch.AArch64.withStackScratch 768 .x5
      (Impl.Sm4Gcm.AArch64.streamFinish (⟨v.gh.impl, v.ctr.impl⟩ : GcmImpl).callees)
    verified := .unscrubbed (streamFinish_framed (⟨v.gh.impl, v.ctr.impl⟩ : GcmImpl) (CtrName.stack_cases v.ctr)) },
  Spec.Sm4.Gcm.streamVerifyApi.artifact AArch64.target {
    suffix := (⟨v.gh.impl, v.ctr.impl⟩ : GcmImpl).suffix
    code := Impl.StackScratch.AArch64.withStackScratch 768 .x6
      (Impl.Sm4Gcm.AArch64.streamVerify (⟨v.gh.impl, v.ctr.impl⟩ : GcmImpl).callees)
    verified := .unscrubbed (streamVerify_framed (⟨v.gh.impl, v.ctr.impl⟩ : GcmImpl) (CtrName.stack_cases v.ctr)) }]

/-- `vg_sm4_gcm_init`, which calls only the implementation of `vg_sm4_ctr32`. -/
def artifactsInit (v : GcmVariant) : List Artifact := [
  Spec.Sm4.Gcm.initApi.artifact AArch64.target {
    suffix := (⟨v.gh.impl, v.ctr.impl⟩ : GcmImpl).ctrSuffix
    code := Impl.StackScratch.AArch64.withStackScratch 768 .x2 (Impl.Sm4Gcm.AArch64.init (⟨v.gh.impl, v.ctr.impl⟩ : GcmImpl).callees)
    verified := .unscrubbed (init_framed (⟨v.gh.impl, v.ctr.impl⟩ : GcmImpl) (CtrName.stack_cases v.ctr)) }]

/-- `vg_sm4_gcm_stream_init` and `vg_sm4_gcm_stream_aad`: AES-GCM's code and
proofs, calling the implementation of `vg_ghash` the variant `v` names (and no
cipher). -/
def artifactsAes (v : GcmVariant) : List Artifact := [
  Spec.Sm4.Gcm.streamInitApi.artifact AArch64.target {
    suffix := v.gh.impl.suffix
    code := Impl.StackScratch.AArch64.withStackScratch 2560 .x4
      (Impl.AesGcm.AArch64.streamInit (Proof.AesGcm.AArch64.GcmVariant.impl ⟨.scalar, .scalar, v.gh, false⟩).callees)
    verified := .unscrubbed (Proof.AesGcm.AArch64.streamInit_framed
      (Proof.AesGcm.AArch64.GcmVariant.impl ⟨.scalar, .scalar, v.gh, false⟩)) },
  Spec.Sm4.Gcm.streamAadApi.artifact AArch64.target {
    suffix := v.gh.impl.suffix
    code := Impl.StackScratch.AArch64.withStackScratch 2560 .x5
      (Impl.AesGcm.AArch64.streamAad (Proof.AesGcm.AArch64.GcmVariant.impl ⟨.scalar, .scalar, v.gh, false⟩).callees)
    verified := .unscrubbed (Proof.AesGcm.AArch64.streamAad_framed
      (Proof.AesGcm.AArch64.GcmVariant.impl ⟨.scalar, .scalar, v.gh, false⟩)) }]

/-- The artifacts calling the implementations the variant `v` names: those
that call only one of the two with the baseline implementation of the other,
of which the other variants would be the same functions. -/
def artifacts (v : GcmVariant) : List Artifact :=
  (match v.gh with
    | .scalar => artifactsInit v
    | .aes | .neon => []) ++
  artifactsOf v ++
  (match v.ctr with
    | .scalar => artifactsAes v
    | .sm4 => [])

end VG.Artifacts.Sm4Gcm.AArch64.Sm4Gcm

namespace VG.Artifacts.Sm4Gcm.AArch64

def artifacts : List Artifact :=
  VG.Proof.Variants.Sm4Gcm.AArch64.variants.flatMap fun v => Sm4Gcm.artifacts v

end VG.Artifacts.Sm4Gcm.AArch64
