module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.Public

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

/-- The initialization and stream functions of the variant `g`. -/
def artifactsOf (g : GcmVariant) : List Artifact := [
  Spec.Gcm.initApi.artifact AArch64.target {
    suffix := g.impl.suffix
    code := Impl.AesGcm.AArch64.Fn.init g.calls
    verified := Proof.AesGcm.AArch64.init_scrubbed g },
  Spec.Gcm.streamInitApi.artifact AArch64.target {
    suffix := g.impl.suffix
    code := Impl.AesGcm.AArch64.Fn.streamInit g.calls
    verified := Proof.AesGcm.AArch64.streamInit_scrubbed g },
  Spec.Gcm.streamAadApi.artifact AArch64.target {
    suffix := g.impl.suffix
    code := Impl.AesGcm.AArch64.Fn.streamAad g.calls
    verified := Proof.AesGcm.AArch64.streamAad_scrubbed g },
  Spec.Gcm.streamEncryptApi.artifact AArch64.target {
    suffix := g.impl.suffix
    code := Impl.AesGcm.AArch64.Fn.streamEncrypt g.calls
    verified := Proof.AesGcm.AArch64.streamEncrypt_scrubbed g },
  Spec.Gcm.streamDecryptApi.artifact AArch64.target {
    suffix := g.impl.suffix
    code := Impl.AesGcm.AArch64.Fn.streamDecrypt g.calls
    verified := Proof.AesGcm.AArch64.streamDecrypt_scrubbed g },
  Spec.Gcm.streamFinishApi.artifact AArch64.target {
    suffix := g.impl.suffix
    code := Impl.AesGcm.AArch64.Fn.streamFinish g.calls
    verified := Proof.AesGcm.AArch64.streamFinish_scrubbed g },
  Spec.Gcm.streamVerifyApi.artifact AArch64.target {
    suffix := g.impl.suffix
    code := Impl.AesGcm.AArch64.Fn.streamVerify g.calls
    verified := Proof.AesGcm.AArch64.streamVerify_scrubbed g }]

/-- The initialization and stream functions of the variant `g`, which call
its implementations by the addresses in `d8` and `d9`. -/
def artifactsDS (g : GcmVariant) : List Artifact := [
  Spec.Gcm.initApi.artifact AArch64.target {
    suffix := g.impl.suffix
    code := Impl.AesGcm.AArch64.Fn.initDS g.calls
    verified := Proof.AesGcm.AArch64.initDS_scrubbed g },
  Spec.Gcm.streamInitApi.artifact AArch64.target {
    suffix := g.impl.suffix
    code := Impl.AesGcm.AArch64.Fn.streamInitDS g.calls
    verified := Proof.AesGcm.AArch64.streamInitDS_scrubbed g },
  Spec.Gcm.streamAadApi.artifact AArch64.target {
    suffix := g.impl.suffix
    code := Impl.AesGcm.AArch64.Fn.streamAadDS g.calls
    verified := Proof.AesGcm.AArch64.streamAadDS_scrubbed g },
  Spec.Gcm.streamEncryptApi.artifact AArch64.target {
    suffix := g.impl.suffix
    code := Impl.AesGcm.AArch64.Fn.streamEncryptDS g.calls
    verified := Proof.AesGcm.AArch64.streamEncryptDS_scrubbed g },
  Spec.Gcm.streamDecryptApi.artifact AArch64.target {
    suffix := g.impl.suffix
    code := Impl.AesGcm.AArch64.Fn.streamDecryptDS g.calls
    verified := Proof.AesGcm.AArch64.streamDecryptDS_scrubbed g },
  Spec.Gcm.streamFinishApi.artifact AArch64.target {
    suffix := g.impl.suffix
    code := Impl.AesGcm.AArch64.Fn.streamFinishDS g.calls
    verified := Proof.AesGcm.AArch64.streamFinishDS_scrubbed g },
  Spec.Gcm.streamVerifyApi.artifact AArch64.target {
    suffix := g.impl.suffix
    code := Impl.AesGcm.AArch64.Fn.streamVerifyDS g.calls
    verified := Proof.AesGcm.AArch64.streamVerifyDS_scrubbed g }]

/-- Contiguous seal over identical or separate buffers, using the same code for each layout. -/
def contiguousArtifact (g : GcmVariant) : Artifact :=
  Spec.Gcm.sealContiguousWithPowersApi.artifact AArch64.target {
    suffix := g.impl.suffix
    code := Impl.AesGcm.AArch64.Contiguous.select g.calls
    verified := Proof.AesGcm.AArch64.Contiguous.public_verified
      (Proof.AesGcm.AArch64.Contiguous.backendFacts g.impl) }

/-- The gather implementation consumes the original input slices on each backend. -/
def gatherArtifact (g : GcmVariant) : Artifact :=
  Spec.Gcm.sealGatherApi.artifact AArch64.target {
    suffix := g.impl.suffix
    code := Impl.AesGcm.AArch64.DirectGather.sealGather g.calls
    verified := Proof.AesGcm.AArch64.DirectGather.sealGather_scrubbed g.impl }

/-- `vg_aes_gcm_seal_with_powers`, `vg_aes_gcm_open_with_powers` and
`vg_aes_gcm_open_to_with_powers` of the variant `g`, calling `w` on the path
for TLS records. -/
def withPowersArtifacts (g : GcmVariant) (w : GhashWithImpl) : List Artifact := [
  Spec.Gcm.sealWithPowersApi.artifact AArch64.target {
    suffix := g.impl.suffix
    code := Impl.AesGcm.AArch64.Fn.sealWithPowers g.calls w.fn
    verified := Proof.AesGcm.AArch64.sealWithPowers_scrubbed g w },
  Spec.Gcm.openWithPowersApi.artifact AArch64.target {
    suffix := g.impl.suffix
    code := Impl.AesGcm.AArch64.Fn.openWithPowers g.calls w.fn
    verified := Proof.AesGcm.AArch64.openWithPowers_scrubbed g w },
  Spec.Gcm.openToWithPowersApi.artifact AArch64.target {
    suffix := g.impl.suffix
    code := Impl.AesGcm.AArch64.Fn.openToWithPowers g.calls w.fn
    verified := Proof.AesGcm.AArch64.openToWithPowers_scrubbed g w }]

/-- `vg_aes_gcm_seal_with_powers`, `vg_aes_gcm_open_with_powers` and
`vg_aes_gcm_open_to_with_powers` of a variant without code that reads the
powers: its `seal`, `open` and `open_to`. -/
def basePwArtifacts (g : GcmVariant) : List Artifact := [
  Spec.Gcm.sealWithPowersApi.artifact AArch64.target {
    suffix := g.impl.suffix
    code := Impl.AesGcm.AArch64.Fn.sealWithPowersBase g.calls
    verified := Proof.AesGcm.AArch64.sealWithPowersBase_scrubbed g },
  Spec.Gcm.openWithPowersApi.artifact AArch64.target {
    suffix := g.impl.suffix
    code := Impl.AesGcm.AArch64.Fn.openWithPowersBase g.calls
    verified := Proof.AesGcm.AArch64.openWithPowersBase_scrubbed g },
  Spec.Gcm.openToWithPowersApi.artifact AArch64.target {
    suffix := g.impl.suffix
    code := Impl.AesGcm.AArch64.Fn.openToWithPowersBase g.calls
    verified := Proof.AesGcm.AArch64.openToWithPowersBase_scrubbed g }]

/-- The artifacts of a variant: the functions it has (`GcmVariant.whole`,
`withPowers`, `basePowers`), calling its implementations directly or by
their addresses (`GcmVariant.direct`, `viaRegs`). -/
def artifactsFor (g : GcmVariant) : List Artifact :=
  (g.whole.flatMap GcmVariant.direct).flatMap artifactsOf ++ (g.whole.flatMap GcmVariant.viaRegs).flatMap artifactsDS ++
    [gatherArtifact g, contiguousArtifact g] ++
    g.withPowers.flatMap (withPowersArtifacts g) ++ g.basePowers.flatMap basePwArtifacts

def artifacts : List Artifact :=
  VG.Proof.Variants.AesGcm.AArch64.variants.flatMap artifactsFor ++ [
    Spec.Gcm.storePowersApi.artifact AArch64.target {
      code := Impl.AesGcm.AArch64.Fn.storePowers
      verified := Proof.AesGcm.AArch64.storePowers_scrubbed },
    Spec.Gcm.storePowersApi.artifact AArch64.target {
      suffix := "_aes"
      code := Impl.Gcm.AArch64.Fn.keyPowers
      verified := Proof.AesGcm.AArch64.storePowersAes_scrubbed }]

end VG.Artifacts.AesGcm.AArch64
