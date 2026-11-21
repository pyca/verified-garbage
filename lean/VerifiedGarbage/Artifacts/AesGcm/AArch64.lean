module

public import VerifiedGarbage.Impl.AesGcm.AArch64.Fn
public import VerifiedGarbage.Impl.Gcm.AArch64.Fn
public import VerifiedGarbage.Proof.AesGcm.AArch64.GhashImpls
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.Variants.AesGcm.AArch64

/-! # AES-GCM (NIST SP 800-38D) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.AesGcm.AArch64

open VG.Proof.AesGcm.AArch64

/-- `vg_aes_gcm_seal`, `vg_aes_gcm_init`, `vg_aes_gcm_open`, `vg_aes_gcm_open_to`, the
stream functions and `vg_aes_gcm_seal_gather` of the variant `g`. -/
def artifactsOf (g : GcmVariant) : List Artifact := [
  Spec.Gcm.sealApi.artifact AArch64.target {
    suffix := g.impl.suffix
    code := Impl.AesGcm.AArch64.Fn.seal g.calls
    verified := .scrubbed (seal_scrubbed g) },
  Spec.Gcm.initApi.artifact AArch64.target {
    suffix := g.impl.suffix
    code := Impl.AesGcm.AArch64.Fn.init g.calls
    verified := .scrubbed (init_scrubbed g) },
  Spec.Gcm.openApi.artifact AArch64.target {
    suffix := g.impl.suffix
    code := Impl.AesGcm.AArch64.Fn.open g.calls
    verified := .scrubbed (open_scrubbed g) },
  Spec.Gcm.openToApi.artifact AArch64.target {
    suffix := g.impl.suffix
    code := Impl.AesGcm.AArch64.Fn.openTo g.calls
    verified := .scrubbed (openTo_scrubbed g) },
  Spec.Gcm.streamInitApi.artifact AArch64.target {
    suffix := g.impl.suffix
    code := Impl.AesGcm.AArch64.Fn.streamInit g.calls
    verified := .scrubbed (streamInit_scrubbed g) },
  Spec.Gcm.streamAadApi.artifact AArch64.target {
    suffix := g.impl.suffix
    code := Impl.AesGcm.AArch64.Fn.streamAad g.calls
    verified := .scrubbed (streamAad_scrubbed g) },
  Spec.Gcm.streamEncryptApi.artifact AArch64.target {
    suffix := g.impl.suffix
    code := Impl.AesGcm.AArch64.Fn.streamEncrypt g.calls
    verified := .scrubbed (streamEncrypt_scrubbed g) },
  Spec.Gcm.streamDecryptApi.artifact AArch64.target {
    suffix := g.impl.suffix
    code := Impl.AesGcm.AArch64.Fn.streamDecrypt g.calls
    verified := .scrubbed (streamDecrypt_scrubbed g) },
  Spec.Gcm.streamFinishApi.artifact AArch64.target {
    suffix := g.impl.suffix
    code := Impl.AesGcm.AArch64.Fn.streamFinish g.calls
    verified := .scrubbed (streamFinish_scrubbed g) },
  Spec.Gcm.streamVerifyApi.artifact AArch64.target {
    suffix := g.impl.suffix
    code := Impl.AesGcm.AArch64.Fn.streamVerify g.calls
    verified := .scrubbed (streamVerify_scrubbed g) },
  Spec.Gcm.sealGatherApi.artifact AArch64.target {
    suffix := g.impl.suffix
    code := Impl.AesGcm.AArch64.Fn.sealGather g.calls
    verified := .scrubbed (sealGather_scrubbed g) }]

/-- `vg_aes_gcm_seal_with_powers`, `vg_aes_gcm_open_with_powers` and
`vg_aes_gcm_open_to_with_powers` of the variant `g`, calling `w` on the path
for TLS records. -/
def withPowersArtifacts (g : GcmVariant) (w : GhashWithImpl) : List Artifact := [
  Spec.Gcm.sealWithPowersApi.artifact AArch64.target {
    suffix := g.impl.suffix
    code := Impl.AesGcm.AArch64.Fn.sealWithPowers g.calls w.fn
    verified := .scrubbed (sealWithPowers_scrubbed g w) },
  Spec.Gcm.openWithPowersApi.artifact AArch64.target {
    suffix := g.impl.suffix
    code := Impl.AesGcm.AArch64.Fn.openWithPowers g.calls w.fn
    verified := .scrubbed (openWithPowers_scrubbed g w) },
  Spec.Gcm.openToWithPowersApi.artifact AArch64.target {
    suffix := g.impl.suffix
    code := Impl.AesGcm.AArch64.Fn.openToWithPowers g.calls w.fn
    verified := .scrubbed (openToWithPowers_scrubbed g w) }]

/-- `vg_aes_gcm_seal_with_powers`, `vg_aes_gcm_open_with_powers` and
`vg_aes_gcm_open_to_with_powers` of a variant without code that reads the
powers: its `seal`, `open` and `open_to`. -/
def basePwArtifacts (g : GcmVariant) : List Artifact := [
  Spec.Gcm.sealWithPowersApi.artifact AArch64.target {
    suffix := g.impl.suffix
    code := Impl.AesGcm.AArch64.Fn.sealWithPowersBase g.calls
    verified := .scrubbed (sealWithPowersBase_scrubbed g) },
  Spec.Gcm.openWithPowersApi.artifact AArch64.target {
    suffix := g.impl.suffix
    code := Impl.AesGcm.AArch64.Fn.openWithPowersBase g.calls
    verified := .scrubbed (openWithPowersBase_scrubbed g) },
  Spec.Gcm.openToWithPowersApi.artifact AArch64.target {
    suffix := g.impl.suffix
    code := Impl.AesGcm.AArch64.Fn.openToWithPowersBase g.calls
    verified := .scrubbed (openToWithPowersBase_scrubbed g) }]

/-- The artifacts of a variant: the functions it has (`GcmVariant.whole`,
`withPowers`, `basePowers`). -/
def artifactsFor (g : GcmVariant) : List Artifact :=
  g.whole.flatMap artifactsOf ++ g.withPowers.flatMap (withPowersArtifacts g) ++
    g.basePowers.flatMap basePwArtifacts

def artifacts : List Artifact :=
  VG.Proof.Variants.AesGcm.AArch64.variants.flatMap artifactsFor ++ [
    Spec.Gcm.storePowersApi.artifact AArch64.target {
      code := Impl.AesGcm.AArch64.Fn.storePowers
      verified := .scrubbed storePowers_scrubbed },
    Spec.Gcm.storePowersApi.artifact AArch64.target {
      suffix := "_aes"
      code := Impl.Gcm.AArch64.Fn.keyPowers
      verified := .scrubbed storePowersAes_scrubbed }]

end VG.Artifacts.AesGcm.AArch64
