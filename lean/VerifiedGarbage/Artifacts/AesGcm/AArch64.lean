module

public import VerifiedGarbage.Impl.Gcm.AArch64.Fn
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

/-- The stream functions of the variant `g`, in frames sized to its
implementations, zeroed whole on return. -/
def artifactsOf (g : GcmVariant) (hg : g ∈ VG.Proof.Variants.AesGcm.AArch64.variants) : List Artifact := [
  Spec.Gcm.streamInitApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
    suffix := g.impl.suffix
    code := Impl.StackScratch.AArch64.withStackScratch (gcmWn g.impl) .x4 (Impl.AesGcm.AArch64.streamInit g.impl.callees)
    verified := streamInit_framedW g.impl }
    Proof.AesGcm.AArch64.Scrub.clear (Proof.AesGcm.AArch64.Scrub.streamInitOk _ (gcmWn_pos g.impl))
    (Proof.AesGcm.AArch64.Scrub.streamInitSide g hg)),
  Spec.Gcm.streamAadApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
    suffix := g.impl.suffix
    code := Impl.StackScratch.AArch64.withStackScratch (gcmWn g.impl) .x5 (Impl.AesGcm.AArch64.streamAad g.impl.callees)
    verified := streamAad_framedW g.impl }
    Proof.AesGcm.AArch64.Scrub.clear (Proof.AesGcm.AArch64.Scrub.streamAadOk _ (gcmWn_pos g.impl))
    (Proof.AesGcm.AArch64.Scrub.streamAadSide g hg)),
  Spec.Gcm.streamEncryptApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
    suffix := g.impl.suffix
    code := Impl.StackScratch.AArch64.withStackScratch (gcmWn g.impl) .x7 (Impl.AesGcm.AArch64.streamEncrypt g.impl.callees)
    verified := Proof.AesGcm.streamEncrypt_keyed (streamEncrypt_framedW g.impl) }
    Proof.AesGcm.AArch64.Scrub.clear (Proof.AesGcm.AArch64.Scrub.streamEncryptOk _ (gcmWn_pos g.impl))
    (Proof.AesGcm.AArch64.Scrub.streamEncryptSide g hg)),
  Spec.Gcm.streamDecryptApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
    suffix := g.impl.suffix
    code := Impl.StackScratch.AArch64.withStackScratch (gcmWn g.impl) .x7 (Impl.AesGcm.AArch64.streamDecrypt g.impl.callees)
    verified := Proof.AesGcm.streamDecrypt_keyed (streamDecrypt_framedW g.impl) }
    Proof.AesGcm.AArch64.Scrub.clear (Proof.AesGcm.AArch64.Scrub.streamDecryptOk _ (gcmWn_pos g.impl))
    (Proof.AesGcm.AArch64.Scrub.streamDecryptSide g hg)),
  Spec.Gcm.streamFinishApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
    suffix := g.impl.suffix
    code := Impl.StackScratch.AArch64.withStackScratch (gcmWn g.impl) .x6 (Impl.AesGcm.AArch64.streamFinish g.impl.callees)
    verified := Proof.AesGcm.streamFinish_keyed (streamFinish_framedW g.impl) }
    Proof.AesGcm.AArch64.Scrub.clear (Proof.AesGcm.AArch64.Scrub.streamFinishOk _ (gcmWn_pos g.impl))
    (Proof.AesGcm.AArch64.Scrub.streamFinishSide g hg)),
  Spec.Gcm.streamVerifyApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
    suffix := g.impl.suffix
    code := Impl.StackScratch.AArch64.withStackScratch (gcmWn g.impl) .x7 (Impl.AesGcm.AArch64.streamVerify g.impl.callees)
    verified := Proof.AesGcm.streamVerify_keyed (streamVerify_framedW g.impl) }
    Proof.AesGcm.AArch64.Scrub.clear (Proof.AesGcm.AArch64.Scrub.streamVerifyOk _ (gcmWn_pos g.impl))
    (Proof.AesGcm.AArch64.Scrub.streamVerifySide g hg))]

/-- `vg_aes_gcm_seal_gather`, calling the instance of `vg_aes_gcm_seal` of the variant `g`. -/
def artifactsGather (g : GcmVariant) (hg : g ∈ VG.Proof.Variants.AesGcm.AArch64.variants) : List Artifact := [
  Spec.Gcm.sealGatherApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
    suffix := g.impl.suffix
    code := Impl.AesGcm.AArch64.SealGather.sealGather
      (Proof.AesGcm.AArch64.Scrub.sealFnW g hg Proof.Gcm.AArch64.Pmull.mulV_keyV).fn
    verified := Proof.AesGcm.sealGather_keyed (Proof.AesGcm.AArch64.Gather.sealGather_verified
      (Proof.AesGcm.AArch64.Scrub.sealFnW g hg Proof.Gcm.AArch64.Pmull.mulV_keyV)) }
    Proof.AesGcm.AArch64.Scrub.clear (Proof.AesGcm.AArch64.Scrub.sealGatherOk _)
    (Proof.AesGcm.AArch64.Scrub.sealGatherSide g hg Proof.Gcm.AArch64.Pmull.mulV_keyV))]

/-- `vg_aes_gcm_seal`, `vg_aes_gcm_init`, `vg_aes_gcm_open` and `vg_aes_gcm_open_to` of the
variant `g`, in frames sized to its implementations, zeroed whole on return. -/
def artifactsScrubbed (g : GcmVariant) (hg : g ∈ VG.Proof.Variants.AesGcm.AArch64.variants) : List Artifact := [
  Spec.Gcm.sealApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
    suffix := g.impl.suffix
    code := Impl.StackScratch.AArch64.withStackArgScratch (gcmWn g.impl + 16) 1 (sealCode g.impl)
    verified := Proof.AesGcm.seal_keyed (sealCode_framedW g.impl Proof.Gcm.AArch64.Pmull.mulV_keyV) }
    Proof.AesGcm.AArch64.Scrub.clear (Proof.AesGcm.AArch64.Scrub.sealOk _)
    (Proof.AesGcm.AArch64.Scrub.sealSide g hg)),
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
def withPowersArtifacts (g : GcmVariant) (hg : g ∈ VG.Proof.Variants.AesGcm.AArch64.variants) (w : GhashWithImpl)
    (hw : w ∈ g.impl.gh.withPowers) : List Artifact :=
  [Spec.Gcm.sealWithPowersApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
    suffix := g.impl.suffix
    code := Impl.StackScratch.AArch64.withStackArgScratch (gcmPwWn g.impl + 32) 2 (sealPwCode g.impl w)
    verified := Proof.AesGcm.sealWithPowers_keyed (sealPwCode_framedW g.impl Proof.Gcm.AArch64.Pmull.mulV_keyV Proof.Gcm.AArch64.Stitch.gh8Ok w) }
    Proof.AesGcm.AArch64.Scrub.clear (Proof.AesGcm.AArch64.Scrub.sealWithPowersOk _)
    (Proof.AesGcm.AArch64.Scrub.sealPwSide g hg w hw)),
  Spec.Gcm.openWithPowersApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
    suffix := g.impl.suffix
    code := Impl.StackScratch.AArch64.withStackArgScratch (gcmPwWn g.impl + 32) 3 (openPwCode g.impl w)
    verified := Proof.AesGcm.openWithPowers_keyed (openPwCode_framedW g.impl Proof.Gcm.AArch64.Pmull.mulV_keyV Proof.Gcm.AArch64.Stitch.gh8Ok w) }
    Proof.AesGcm.AArch64.Scrub.clear (Proof.AesGcm.AArch64.Scrub.openWithPowersOk _)
    (Proof.AesGcm.AArch64.Scrub.openPwSide g hg w hw)),
  Spec.Gcm.openToWithPowersApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
    suffix := g.impl.suffix
    code := Impl.StackScratch.AArch64.withStackArgScratch (gcmPwWn g.impl + 48) 5 (openToPwCode g.impl w)
    verified := Proof.AesGcm.openToWithPowers_keyed (openToPwCode_framedW g.impl Proof.Gcm.AArch64.Pmull.mulV_keyV Proof.Gcm.AArch64.Stitch.gh8Ok w) }
    Proof.AesGcm.AArch64.Scrub.clear (Proof.AesGcm.AArch64.Scrub.openToWithPowersOk _)
    (Proof.AesGcm.AArch64.Scrub.openToPwSide g hg w hw))]

/-- `vg_aes_gcm_seal_with_powers`, `vg_aes_gcm_open_with_powers` and
`vg_aes_gcm_open_to_with_powers` of implementations without code that reads
the powers: their `seal`, `open` and `open_to`. -/
def basePwArtifacts (g : GcmVariant) (hg : g ∈ VG.Proof.Variants.AesGcm.AArch64.variants) : List Artifact :=
  [Spec.Gcm.sealWithPowersApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
    suffix := g.impl.suffix
    code := Impl.StackScratch.AArch64.withStackArgScratch 2576 1 (sealCode g.impl)
    verified := sealBasePw_verified g.impl Proof.Gcm.AArch64.Pmull.mulV_keyV }
    Proof.AesGcm.AArch64.Scrub.clear (Proof.AesGcm.AArch64.Scrub.sealWithPowersOk _)
    (Proof.AesGcm.AArch64.Scrub.sealBasePwSide g hg)),
  Spec.Gcm.openWithPowersApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
    suffix := g.impl.suffix
    code := Impl.StackScratch.AArch64.withStackArgScratch 2592 2 (openCode g.impl)
    verified := openBasePw_verified g.impl Proof.Gcm.AArch64.Pmull.mulV_keyV }
    Proof.AesGcm.AArch64.Scrub.clear (Proof.AesGcm.AArch64.Scrub.openWithPowersOk _)
    (Proof.AesGcm.AArch64.Scrub.openBasePwSide g hg)),
  Spec.Gcm.openToWithPowersApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
    suffix := g.impl.suffix
    code := Impl.StackScratch.AArch64.withStackArgScratch 2608 4 (openToCode g.impl)
    verified := openToBasePw_verified g.impl Proof.Gcm.AArch64.Pmull.mulV_keyV }
    Proof.AesGcm.AArch64.Scrub.clear (Proof.AesGcm.AArch64.Scrub.openToWithPowersOk _)
    (Proof.AesGcm.AArch64.Scrub.openToBasePwSide g hg))]

/-- The artifacts of a variant, from the implementations it names: those that
do not use the stitched loops only for the variant without them, of which
the variant with them would be the same functions. -/
def artifactsFor (v : GcmVariant) (hv : v ∈ VG.Proof.Variants.AesGcm.AArch64.variants) : List Artifact :=
  (if v.stitch then [] else
    artifactsScrubbed v hv ++ artifactsOf v hv ++ artifactsGather v hv) ++
    (v.impl.gh.withPowers.attach.map fun ⟨w, hw⟩ => withPowersArtifacts v hv w hw).getD
      (if v.stitch then [] else basePwArtifacts v hv)

def artifacts : List Artifact :=
  (VG.Proof.Variants.AesGcm.AArch64.variants.attach.flatMap fun ⟨v, hv⟩ => artifactsFor v hv) ++
  [
    Spec.Gcm.storePowersApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
      code := Impl.StackScratch.AArch64.withStackScratch 80 .x2 Impl.Gcm.AArch64.keyPowers
      verified := Proof.Gcm.AArch64.KeyPowers.keyPowers_framed }
      Proof.AesGcm.AArch64.Scrub.clear Proof.AesGcm.AArch64.Scrub.storePowersOk80
      Proof.AesGcm.AArch64.Scrub.storePowersSide),
    Spec.Gcm.storePowersApi.artifact AArch64.target {
      suffix := "_aes"
      code := Impl.Gcm.AArch64.Fn.keyPowers
      verified := .scrubbed ⟨Proof.Gcm.AArch64.Pmull.keyPowersCleared_verified,
        Proof.Gcm.AArch64.Pmull.keyPowersCleared_noResidue _⟩ }]

end VG.Artifacts.AesGcm.AArch64
