module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Instances
public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.Instances
public import VerifiedGarbage.Proof.AesGcm.AArch64.GhashImpls
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.OpenVerified
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.SealPw
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.OpenPw
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
import VerifiedGarbage.Proof.AesGcm.AArch64.BodyCT
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Entry
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.OpenCT
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Pad
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Run
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Seal
import VerifiedGarbage.Proof.AesGcm.AArch64.Fn
import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.CT
import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.Fn
import VerifiedGarbage.Proof.AesGcm.AArch64.Init
import VerifiedGarbage.Proof.AesGcm.AArch64.OpenCT
import VerifiedGarbage.Proof.AesGcm.AArch64.PieceCT
import VerifiedGarbage.Proof.AesGcm.AArch64.Rel
import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.Open
import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.OpenCT
import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.OpenPw
import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.Run
import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.SealPw
import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.Verified
import VerifiedGarbage.Proof.AesGcm.AArch64.StreamCryptCT
import VerifiedGarbage.Proof.AesGcm.AArch64.StreamFinish
import VerifiedGarbage.Proof.AesGcm.AArch64.StreamVerify
import VerifiedGarbage.Proof.AesGcm.CtxFrame
import VerifiedGarbage.Proof.AesGcm.ScratchPrepared
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Final
import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Loop
import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Ok
import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Steps
import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Weave
import VerifiedGarbage.Proof.Gcm.Bits
import VerifiedGarbage.Proof.Gcm.Powers
import VerifiedGarbage.Proof.Gcm.SealGather

/-! # AES-GCM (NIST SP 800-38D) on AArch64 -/

@[expose] public section

namespace VG.Generic.AesGcm.AArch64.AesGcm

open VG.Proof.AesGcm.AArch64

/-- The artifacts calling the implementations `v`. -/
def artifactsOf (v : GcmImpl) : List Artifact := [
  Spec.Gcm.initApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.StackScratch.AArch64.withStackScratch 2560 .x3 (Impl.AesGcm.AArch64.init v.callees)
    stack := 2560
    verified := init_framed v
    features := v.ctr.features },
  Spec.Gcm.sealApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.StackScratch.AArch64.withStackArgScratch 2576 1 (sealCode v)
    stack := 2576
    verified := sealCode_framed v Proof.Gcm.AArch64.Pmull.mulV_keyV
    features := v.features },
  Spec.Gcm.openApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.StackScratch.AArch64.withStackArgScratch 2592 2 (openCode v)
    stack := 2592
    verified := openCode_framed v Proof.Gcm.AArch64.Pmull.mulV_keyV
    features := v.features },
  Spec.Gcm.streamInitApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.StackScratch.AArch64.withStackScratch 2560 .x4 (Impl.AesGcm.AArch64.streamInit v.callees)
    stack := 2560
    verified := streamInit_framed v
    features := v.gh.features },
  Spec.Gcm.streamAadApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.StackScratch.AArch64.withStackScratch 2560 .x5 (Impl.AesGcm.AArch64.streamAad v.callees)
    stack := 2560
    verified := streamAad_framed v
    features := v.gh.features },
  Spec.Gcm.streamEncryptApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.StackScratch.AArch64.withStackScratch 2560 .x7 (Impl.AesGcm.AArch64.streamEncrypt v.callees)
    stack := 2560
    verified := streamEncrypt_framed v
    features := v.features },
  Spec.Gcm.streamDecryptApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.StackScratch.AArch64.withStackScratch 2560 .x7 (Impl.AesGcm.AArch64.streamDecrypt v.callees)
    stack := 2560
    verified := streamDecrypt_framed v
    features := v.features },
  Spec.Gcm.streamFinishApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.StackScratch.AArch64.withStackScratch 2560 .x6
      (Impl.AesGcm.AArch64.streamFinish v.callees)
    stack := 2560
    verified := streamFinish_framed v
    features := v.features },
  Spec.Gcm.streamVerifyApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.StackScratch.AArch64.withStackScratch 2560 .x7
      (Impl.AesGcm.AArch64.streamVerify v.callees)
    stack := 2560
    verified := streamVerify_framed v
    features := v.features }]

/-- `vg_aes_gcm_seal_gather`, calling the instance of `vg_aes_gcm_seal` of the implementations `v`. -/
def artifactsGather (v : GcmImpl) : List Artifact := [
  Spec.Gcm.sealGatherApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.AesGcm.AArch64.SealGather.sealGather (Proof.AesGcm.AArch64.sealFn v Proof.Gcm.AArch64.Pmull.mulV_keyV).fn
    stack := 2592
    verified := Proof.AesGcm.AArch64.Gather.sealGather_verified (Proof.AesGcm.AArch64.sealFn v Proof.Gcm.AArch64.Pmull.mulV_keyV)
    features := v.features }]

/-- `vg_aes_gcm_seal_with_powers` and `vg_aes_gcm_open_with_powers`, calling
`g` on the path for TLS records. -/
def withPowersArtifacts (v : GcmImpl) (g : GhashWithImpl) : List Artifact :=
  [Spec.Gcm.sealWithPowersApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.StackScratch.AArch64.withStackArgScratch 2592 2 (sealPwCode v g)
    stack := 2592
    verified := sealPwCode_framed v Proof.Gcm.AArch64.Pmull.mulV_keyV Proof.Gcm.AArch64.Stitch.gh8Ok g
    features := v.stitchFeatures },
  Spec.Gcm.openWithPowersApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.StackScratch.AArch64.withStackArgScratch 2592 3 (openPwCode v g)
    stack := 2592
    verified := openPwCode_framed v Proof.Gcm.AArch64.Pmull.mulV_keyV Proof.Gcm.AArch64.Stitch.gh8Ok g
    features := v.stitchFeatures }]

/-- The artifacts of a variant, from the implementations it names. -/
def artifacts (v : GcmVariant) : List Artifact :=
  artifactsOf v.impl ++ artifactsGather v.impl ++
    (v.impl.gh.withPowers.map (withPowersArtifacts v.impl)).getD []

end VG.Generic.AesGcm.AArch64.AesGcm
