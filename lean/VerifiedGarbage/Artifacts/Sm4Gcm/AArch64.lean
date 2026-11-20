module

public import VerifiedGarbage.Impl.Sm4Gcm.AArch64.Fn
public import VerifiedGarbage.Impl.AesGcm.AArch64.Fn
public import VerifiedGarbage.Proof.AesGcm.AArch64.GhashImpls
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.Variants.Sm4Gcm.AArch64

/-! # SM4-GCM (NIST SP 800-38D, RFC 8998) on AArch64 -/

@[expose] public section

-- SM4-GCM (NIST SP 800-38D with SM4, RFC 8998) on AArch64
namespace VG.Artifacts.Sm4Gcm.AArch64.Sm4Gcm

open VG.Proof.Sm4Gcm.AArch64

/-- The artifacts calling the implementations the variant `v` names. -/
def artifactsOf (v : GcmVariant) : List Artifact := [
  Spec.Sm4.Gcm.sealApi.artifact AArch64.target {
    suffix := v.impl.suffix
    code := Impl.Sm4Gcm.AArch64.Fn.«seal» v.calls
    verified := .scrubbed (seal_scrubbed v) },
  Spec.Sm4.Gcm.openApi.artifact AArch64.target {
    suffix := v.impl.suffix
    code := Impl.Sm4Gcm.AArch64.Fn.«open» v.calls
    verified := .scrubbed (open_scrubbed v) },
  Spec.Sm4.Gcm.streamEncryptApi.artifact AArch64.target {
    suffix := v.impl.suffix
    code := Impl.Sm4Gcm.AArch64.Fn.streamEncrypt v.calls
    verified := .scrubbed (streamEncrypt_scrubbed v) },
  Spec.Sm4.Gcm.streamDecryptApi.artifact AArch64.target {
    suffix := v.impl.suffix
    code := Impl.Sm4Gcm.AArch64.Fn.streamDecrypt v.calls
    verified := .scrubbed (streamDecrypt_scrubbed v) },
  Spec.Sm4.Gcm.streamFinishApi.artifact AArch64.target {
    suffix := v.impl.suffix
    code := Impl.Sm4Gcm.AArch64.Fn.streamFinish v.calls
    verified := .scrubbed (streamFinish_scrubbed v) },
  Spec.Sm4.Gcm.streamVerifyApi.artifact AArch64.target {
    suffix := v.impl.suffix
    code := Impl.Sm4Gcm.AArch64.Fn.streamVerify v.calls
    verified := .scrubbed (streamVerify_scrubbed v) }]

/-- `vg_sm4_gcm_init`, which calls only the implementation of `vg_sm4_ctr32`. -/
def artifactsInit (v : GcmVariant) : List Artifact := [
  Spec.Sm4.Gcm.initApi.artifact AArch64.target {
    suffix := v.impl.ctrSuffix
    code := Impl.Sm4Gcm.AArch64.Fn.init v.calls
    verified := .scrubbed (init_scrubbed v) }]

/-- `vg_sm4_gcm_stream_init` and `vg_sm4_gcm_stream_aad`: AES-GCM's code and
proofs, calling the implementation of `vg_ghash` the variant `v` names (and no
cipher). -/
def artifactsAes (v : GcmVariant) : List Artifact := [
  Spec.Sm4.Gcm.streamInitApi.artifact AArch64.target {
    suffix := v.gh.impl.suffix
    code := Impl.AesGcm.AArch64.Fn.streamInit v.aes.calls
    verified := .scrubbed (Proof.AesGcm.AArch64.streamInit_scrubbed v.aes) },
  Spec.Sm4.Gcm.streamAadApi.artifact AArch64.target {
    suffix := v.gh.impl.suffix
    code := Impl.AesGcm.AArch64.Fn.streamAad v.aes.calls
    verified := .scrubbed (Proof.AesGcm.AArch64.streamAad_scrubbed v.aes) }]

/-- The artifacts calling the implementations the variant `v` names: those
that call only one of the two with the baseline implementation of the other
(`GcmVariant.ctrOnly`, `ghOnly`), of which the other variants would be the
same functions. -/
def artifacts (v : GcmVariant) : List Artifact :=
  v.ctrOnly.flatMap artifactsInit ++ artifactsOf v ++ v.ghOnly.flatMap artifactsAes

end VG.Artifacts.Sm4Gcm.AArch64.Sm4Gcm

namespace VG.Artifacts.Sm4Gcm.AArch64

def artifacts : List Artifact :=
  VG.Proof.Variants.Sm4Gcm.AArch64.variants.flatMap Sm4Gcm.artifacts

end VG.Artifacts.Sm4Gcm.AArch64
