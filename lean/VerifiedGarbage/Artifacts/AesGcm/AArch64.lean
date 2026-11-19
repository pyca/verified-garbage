module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Instances
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.OpenTo
public import VerifiedGarbage.Proof.AesGcm.RoundsTo
public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.Instances
public import VerifiedGarbage.Proof.AesGcm.AArch64.GhashImpls
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.OpenVerified
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.SealPw
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.OpenPw
public import VerifiedGarbage.Proof.AesGcm.AArch64.BasePw
import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
public import VerifiedGarbage.Proof.AesGcm.AArch64.BodyCT
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Entry
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.OpenCT
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Pad
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Run
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Seal
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fn
public import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.CT
public import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.Fn
public import VerifiedGarbage.Proof.AesGcm.AArch64.Init
public import VerifiedGarbage.Proof.AesGcm.AArch64.OpenCT
public import VerifiedGarbage.Proof.AesGcm.AArch64.PieceCT
public import VerifiedGarbage.Proof.AesGcm.AArch64.Rel
public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.Open
public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.OpenCT
public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.OpenPw
public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.Run
public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.SealPw
public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.Verified
public import VerifiedGarbage.Proof.AesGcm.AArch64.StreamCryptCT
public import VerifiedGarbage.Proof.AesGcm.AArch64.StreamFinish
public import VerifiedGarbage.Proof.AesGcm.AArch64.StreamVerify
public import VerifiedGarbage.Proof.AesGcm.CtxFrame
public import VerifiedGarbage.Proof.AesGcm.ScratchPrepared
public import VerifiedGarbage.Proof.Cmac.Frame
public import VerifiedGarbage.Proof.Cmac.Spec
public import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.Framework.AArch64.RelCT
public import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Range
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Final
public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Loop
public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Ok
public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Steps
public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Weave
public import VerifiedGarbage.Proof.Gcm.Bits
public import VerifiedGarbage.Proof.Gcm.Powers
public import VerifiedGarbage.Proof.Gcm.SealGather
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.Variants.AesGcm.AArch64
public import VerifiedGarbage.Proof.Gcm.AArch64.Pmull.Ghash
public import VerifiedGarbage.Proof.Gcm.AArch64.KeyPowers
public import VerifiedGarbage.Proof.AesGcm.AArch64.Scrub
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved

/-! # AES-GCM (NIST SP 800-38D) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.AesGcm.AArch64

open VG.Proof.AesGcm.AArch64

/-- The artifacts calling the implementations `v`. -/
def artifactsOf (v : GcmImpl) : List Artifact := [
  Spec.Gcm.sealApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.StackScratch.AArch64.withStackArgScratch 2576 1 (sealCode v)
    verified := .unscrubbed (Proof.AesGcm.seal_keyed (sealCode_framed v Proof.Gcm.AArch64.Pmull.mulV_keyV)) },
  Spec.Gcm.streamInitApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.StackScratch.AArch64.withStackScratch 2560 .x4 (Impl.AesGcm.AArch64.streamInit v.callees)
    verified := .unscrubbed (streamInit_framed v) },
  Spec.Gcm.streamAadApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.StackScratch.AArch64.withStackScratch 2560 .x5 (Impl.AesGcm.AArch64.streamAad v.callees)
    verified := .unscrubbed (streamAad_framed v) },
  Spec.Gcm.streamEncryptApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.StackScratch.AArch64.withStackScratch 2560 .x7 (Impl.AesGcm.AArch64.streamEncrypt v.callees)
    verified := .unscrubbed (Proof.AesGcm.streamEncrypt_keyed (streamEncrypt_framed v)) },
  Spec.Gcm.streamDecryptApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.StackScratch.AArch64.withStackScratch 2560 .x7 (Impl.AesGcm.AArch64.streamDecrypt v.callees)
    verified := .unscrubbed (Proof.AesGcm.streamDecrypt_keyed (streamDecrypt_framed v)) },
  Spec.Gcm.streamFinishApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.StackScratch.AArch64.withStackScratch 2560 .x6
      (Impl.AesGcm.AArch64.streamFinish v.callees)
    verified := .unscrubbed (Proof.AesGcm.streamFinish_keyed (streamFinish_framed v)) },
  Spec.Gcm.streamVerifyApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.StackScratch.AArch64.withStackScratch 2560 .x7
      (Impl.AesGcm.AArch64.streamVerify v.callees)
    verified := .unscrubbed (Proof.AesGcm.streamVerify_keyed (streamVerify_framed v)) }]

/-- `vg_aes_gcm_seal_gather`, calling the instance of `vg_aes_gcm_seal` of the implementations `v`. -/
def artifactsGather (v : GcmImpl) : List Artifact := [
  Spec.Gcm.sealGatherApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.AesGcm.AArch64.SealGather.sealGather (Proof.AesGcm.AArch64.sealFn v Proof.Gcm.AArch64.Pmull.mulV_keyV).fn
    verified := .unscrubbed (Proof.AesGcm.sealGather_keyed (Proof.AesGcm.AArch64.Gather.sealGather_verified (Proof.AesGcm.AArch64.sealFn v Proof.Gcm.AArch64.Pmull.mulV_keyV))) }]

/-- `vg_aes_gcm_init`, `vg_aes_gcm_open` and `vg_aes_gcm_open_to` of the
variant `g`, in frames sized to its implementations, zeroed whole on return. -/
def artifactsScrubbed (g : GcmVariant) (hg : g ∈ VG.Proof.Variants.AesGcm.AArch64.variants) : List Artifact := [
  Spec.Gcm.initApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
    suffix := g.impl.suffix
    code := Impl.StackScratch.AArch64.withStackScratch (gcmInitWn g.impl) .x3 (Impl.AesGcm.AArch64.init g.impl.callees)
    verified := init_framedW g.impl }
    Proof.AesGcm.AArch64.Scrub.clear (Proof.AesGcm.AArch64.Scrub.initOkW g.impl)
    (Proof.AesGcm.AArch64.Scrub.initSide g hg)),
  Spec.Gcm.openApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
    suffix := g.impl.suffix
    code := Impl.StackScratch.AArch64.withStackArgScratch (gcmWn g.impl + 32) 2 (openCode g.impl)
    verified := Proof.AesGcm.open_keyed (openCode_framedW g.impl Proof.Gcm.AArch64.Pmull.mulV_keyV) }
    Proof.AesGcm.AArch64.Scrub.clear (Proof.AesGcm.AArch64.Scrub.openOk _)
    (Proof.AesGcm.AArch64.Scrub.openSide g hg)),
  Spec.Gcm.openToApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
    suffix := g.impl.suffix
    code := Impl.StackScratch.AArch64.withStackArgScratch (gcmWn g.impl + 48) 4 (openToCode g.impl)
    verified := Proof.AesGcm.openTo_keyed (openToCode_framedW g.impl Proof.Gcm.AArch64.Pmull.mulV_keyV) }
    Proof.AesGcm.AArch64.Scrub.clear (Proof.AesGcm.AArch64.Scrub.openToOk _)
    (Proof.AesGcm.AArch64.Scrub.openToSide g hg))]

/-- `vg_aes_gcm_seal_with_powers`, `vg_aes_gcm_open_with_powers` and
`vg_aes_gcm_open_to_with_powers`, calling `g` on the path for TLS records:
`open_to` in one pass, decrypting from `src` to `dst` (with the interleaved
loops if `v.stitch`, as `open`). -/
def withPowersArtifacts (v : GcmImpl) (g : GhashWithImpl) : List Artifact :=
  [Spec.Gcm.sealWithPowersApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.StackScratch.AArch64.withStackArgScratch 2592 2 (sealPwCode v g)
    verified := .unscrubbed (Proof.AesGcm.sealWithPowers_keyed (sealPwCode_framed v Proof.Gcm.AArch64.Pmull.mulV_keyV Proof.Gcm.AArch64.Stitch.gh8Ok g)) },
  Spec.Gcm.openWithPowersApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.StackScratch.AArch64.withStackArgScratch 2592 3 (openPwCode v g)
    verified := .unscrubbed (Proof.AesGcm.openWithPowers_keyed (openPwCode_framed v Proof.Gcm.AArch64.Pmull.mulV_keyV Proof.Gcm.AArch64.Stitch.gh8Ok g)) },
  Spec.Gcm.openToWithPowersApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.StackScratch.AArch64.withStackArgScratch 2608 5 (openToPwCode v g)
    verified := .unscrubbed (Proof.AesGcm.openToWithPowers_keyed (openToPwCode_framed v Proof.Gcm.AArch64.Pmull.mulV_keyV Proof.Gcm.AArch64.Stitch.gh8Ok g)) }]

/-- `vg_aes_gcm_seal_with_powers`, `vg_aes_gcm_open_with_powers` and
`vg_aes_gcm_open_to_with_powers` of implementations without code that reads
the powers: their `seal`, `open` and `open_to`. -/
def basePwArtifacts (v : GcmImpl) : List Artifact :=
  [Spec.Gcm.sealWithPowersApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.StackScratch.AArch64.withStackArgScratch 2576 1 (sealCode v)
    verified := .unscrubbed (sealBasePw_verified v Proof.Gcm.AArch64.Pmull.mulV_keyV) },
  Spec.Gcm.openWithPowersApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.StackScratch.AArch64.withStackArgScratch 2592 2 (openCode v)
    verified := .unscrubbed (openBasePw_verified v Proof.Gcm.AArch64.Pmull.mulV_keyV) },
  Spec.Gcm.openToWithPowersApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.StackScratch.AArch64.withStackArgScratch 2608 4 (openToCode v)
    verified := .unscrubbed (openToBasePw_verified v Proof.Gcm.AArch64.Pmull.mulV_keyV) }]

/-- The artifacts of a variant, from the implementations it names: those that
do not use the stitched loops only for the variant without them, of which
the variant with them would be the same functions. -/
def artifactsFor (v : GcmVariant) (hv : v ∈ VG.Proof.Variants.AesGcm.AArch64.variants) : List Artifact :=
  (if v.stitch then [] else
    artifactsScrubbed v hv ++ artifactsOf v.impl ++ artifactsGather v.impl) ++
    (v.impl.gh.withPowers.map (withPowersArtifacts v.impl)).getD
      (if v.stitch then [] else basePwArtifacts v.impl)

def artifacts : List Artifact :=
  (VG.Proof.Variants.AesGcm.AArch64.variants.attach.flatMap fun ⟨v, hv⟩ => artifactsFor v hv) ++
  [
    Spec.Gcm.storePowersApi.artifact AArch64.target {
      code := Impl.StackScratch.AArch64.withStackScratch 80 .x2 Impl.Gcm.AArch64.keyPowers
      verified := .unscrubbed Proof.Gcm.AArch64.KeyPowers.keyPowers_framed },
    Spec.Gcm.storePowersApi.artifact AArch64.target {
      suffix := "_aes"
      code := Proof.Gcm.AArch64.Pmull.keyPowersCleared
      verified := Proof.Gcm.AArch64.Pmull.keyPowersCleared_verified
      residue := some ⟨Proof.Gcm.AArch64.Pmull.keyPowersCleared_noResidue _⟩ }]

end VG.Artifacts.AesGcm.AArch64
