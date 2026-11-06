module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Instances
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.X86_64.Registration
import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.Short
import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.Gather
import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.StreamTo
import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.BlocksTo
import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.Verified
import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.BlocksVerified
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksVerifiedP
public import VerifiedGarbage.Proof.Framework.X86_64.Registration
public import VerifiedGarbage.TCB.X86_64.Print

/-! # AES-GCM (NIST SP 800-38D) on x86-64 -/

@[expose] public section

namespace VG.Generic.AesGcm.X86_64.AesGcm

open VG.Proof.AesGcm.X86_64

/-- The artifacts calling the implementations `v`. -/
def artifactsOf (v : GcmImpl) : List Artifact := [
  Spec.Gcm.initApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackScratch 2568 .rcx (Impl.AesGcm.X86_64.init v.callees)
    stack := 2576
    verified := init_framed v
    spSafe := X86_64.withStackScratch_spSafe_of (init_spSafe v)
    features := (v.ctr.features ++ v.key.features).dedup },
  Spec.Gcm.sealApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 2600 3 (v.sealCode v.callees)
    stack := 2624
    verified := Proof.AesGcm.seal_keyed (sealSel_framed v Short.shortFacts)
    spSafe := X86_64.withStackArgScratch_spSafe (sealCode_spSafe v v.blkB)
    features := v.features },
  Spec.Gcm.openApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 2608 4 (v.openCode v.callees)
    stack := 2632
    verified := Proof.AesGcm.open_keyed (openSel_framed v Short.shortFacts)
    spSafe := X86_64.withStackArgScratch_spSafe (openCode_spSafe v v.blkB)
    features := v.features },
  Spec.Gcm.openToApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.AesGcm.X86_64.OpenTo.openTo v.copyW (openFn v).fn
    stack := 2728
    verified := Proof.AesGcm.openTo_keyed (OpenTo.openTo_verified v.copyW (openFn v))
    spSafe := OpenTo.openTo_spAll v.copyW _ (openFn v).spAll
    features := v.features },
  Spec.Gcm.streamInitApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackScratch 2568 .r8
      (Impl.AesGcm.X86_64.streamInit v.callees)
    stack := 2576
    verified := streamInit_framed v
    spSafe := X86_64.withStackScratch_spSafe_of (streamInit_spSafe v)
    features := v.gh.features },
  Spec.Gcm.streamAadApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackScratch 2568 .r9
      (Impl.AesGcm.X86_64.streamAad v.callees)
    stack := 2576
    verified := streamAad_framed v
    spSafe := X86_64.withStackScratch_spSafe_of (streamAad_spSafe v)
    features := v.gh.features },
  Spec.Gcm.streamEncryptApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncrypt v.callees)
    stack := 2608
    verified := Proof.AesGcm.streamEncrypt_keyed (streamEncrypt_framed v)
    spSafe := X86_64.withStackArgScratch_spSafe (streamEncrypt_spSafe v)
    features := v.features },
  Spec.Gcm.streamDecryptApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamDecrypt v.callees)
    stack := 2608
    verified := Proof.AesGcm.streamDecrypt_keyed (streamDecrypt_framed v)
    spSafe := X86_64.withStackArgScratch_spSafe (streamDecrypt_spSafe v)
    features := v.features },
  Spec.Gcm.streamFinishApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 2576 0 (Impl.AesGcm.X86_64.streamFinish v.callees)
    stack := 2584
    verified := Proof.AesGcm.streamFinish_keyed (streamFinish_framed v)
    spSafe := X86_64.withStackArgScratch_spSafe (streamFinish_spSafe v)
    features := (v.ctr.features ++ v.gh.features).dedup },
  Spec.Gcm.streamVerifyApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamVerify v.callees)
    stack := 2592
    verified := Proof.AesGcm.streamVerify_keyed (streamVerify_framed v)
    spSafe := X86_64.withStackArgScratch_spSafe (streamVerify_spSafe v)
    features := (v.ctr.features ++ v.gh.features).dedup }]

/-- The `_precomputed` artifacts calling the implementations `v`. -/
def artifactsP (v : GcmImpl) : List Artifact := [
  Spec.Gcm.initPrecomputedApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackScratch 2568 .rcx (Impl.AesGcm.X86_64.initPrecomputed v.callees)
    stack := 2576
    verified := initP_framed v
    spSafe := X86_64.withStackScratch_spSafe_of (initP_spSafe v)
    features := (v.ctr.features ++ v.key.features ++ v.gh.features).dedup },
  Spec.Gcm.sealPrecomputedApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 2600 3 (v.sealCode (v.withBlk v.blkP))
    stack := 2624
    verified := Proof.AesGcm.sealPrecomputed_keyed (sealSelP_framed v Short.shortFacts)
    spSafe := X86_64.withStackArgScratch_spSafe (sealCode_spSafe v v.blkP)
    features := v.features },
  Spec.Gcm.openPrecomputedApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 2608 4 (v.openCode (v.withBlk v.blkP))
    stack := 2632
    verified := Proof.AesGcm.openPrecomputed_keyed (openSelP_framed v Short.shortFacts)
    spSafe := X86_64.withStackArgScratch_spSafe (openCode_spSafe v v.blkP)
    features := v.features },
  Spec.Gcm.streamEncryptPrecomputedApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 2584 1
      (Impl.AesGcm.X86_64.streamEncrypt (v.withBlk v.blkP))
    stack := 2608
    verified := Proof.AesGcm.streamEncryptPrecomputed_keyed (streamEncryptP_framed v)
    spSafe := X86_64.withStackArgScratch_spSafe (streamEncryptM_spSafe v v.blkP)
    features := v.features },
  Spec.Gcm.streamDecryptPrecomputedApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 2584 1
      (Impl.AesGcm.X86_64.streamDecrypt (v.withBlk v.blkP))
    stack := 2608
    verified := Proof.AesGcm.streamDecryptPrecomputed_keyed (streamDecryptP_framed v)
    spSafe := X86_64.withStackArgScratch_spSafe (streamDecryptM_spSafe v v.blkP)
    features := v.features }]

/-- `vg_aes_gcm_seal_gather` calling the implementations `v`, and the
`_precomputed` one if its loops read the powers from the key context. -/
def artifactsGather (v : GcmVariant) : List Artifact :=
  [Spec.Gcm.sealGatherApi.artifact X86_64.target {
    suffix := v.impl.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 240 5
      (Impl.AesGcm.X86_64.SealGather.sealGather (shortFn v).quick (shortFn v).fast (shortFn v).test
        (shortFn v).code (initFn v.impl).fn
        (aadFn v.impl).fn (toFn v).fn (finFn v.impl).fn)
    stack := 5128
    verified := Proof.AesGcm.sealGather_keyed (Gather.sealGather_framed (shortFn v) (initFn v.impl) (aadFn v.impl) (toFn v)
      (finFn v.impl))
    spSafe := X86_64.withStackArgScratch_spSafe
      (Gather.sealGather_spAll (shortFn v) (initFn v.impl) (aadFn v.impl) (toFn v)
        (finFn v.impl))
    features := v.impl.features }] ++
  if v.impl.stitchP.isSome && v.stitchR.isNone then
    [Spec.Gcm.sealGatherPrecomputedApi.artifact X86_64.target {
      suffix := v.impl.suffix
      code := Impl.StackScratch.X86_64.withStackArgScratch 240 5
        (Impl.AesGcm.X86_64.SealGather.sealGather (shortFnP v).quick (shortFnP v).fast (shortFnP v).test
        (shortFnP v).code (initFn v.impl).fn
          (aadFn v.impl).fn (toFnP v).fn (finFn v.impl).fn)
      stack := 5128
      verified := Proof.AesGcm.sealGatherPrecomputed_keyed (Gather.sealGatherP_framed (shortFnP v) (initFn v.impl) (aadFn v.impl)
        (toFnP v) (finFn v.impl))
      spSafe := X86_64.withStackArgScratch_spSafe
        (Gather.sealGather_spAll (shortFnP v) (initFn v.impl) (aadFn v.impl) (toFnP v)
          (finFn v.impl))
      features := v.impl.features }]
  else []

def artifactsR (v : GcmVariant) : List Artifact := [
  Spec.Gcm.sealPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 2600 3 (v.impl.sealCodeP (v.impl.withBlk (blkR v)))
    stack := 2624
    verified := Proof.AesGcm.sealPrepared_keyed (sealSelPrepared_framed v.impl (blkR v) Short.shortFacts)
    spSafe := X86_64.withStackArgScratch_spSafe (sealCodeP_spSafe v.impl (blkR v))
    features := v.impl.features },
  Spec.Gcm.openPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 2608 4 (v.impl.openCodeP (v.impl.withBlk (blkR v)))
    stack := 2632
    verified := Proof.AesGcm.openPrepared_keyed (openSelPrepared_framed v.impl (blkR v) Short.shortFacts)
    spSafe := X86_64.withStackArgScratch_spSafe (openCodeP_spSafe v.impl (blkR v))
    features := v.impl.features },
  Spec.Gcm.openToPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    code := openToCodeR v
    stack := openToStackR v
    verified := Proof.AesGcm.openToPrepared_keyed (openToCodeR_verified v)
    spSafe := openToCodeR_spAll v
    features := v.impl.features },
  Spec.Gcm.streamEncryptPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 2584 1
      (Impl.AesGcm.X86_64.streamEncrypt (v.impl.withBlk (blkR v)))
    stack := 2608
    verified := Proof.AesGcm.streamEncryptPrepared_keyed (streamEncryptPrepared_framed v.impl (blkR v))
    spSafe := X86_64.withStackArgScratch_spSafe (streamEncryptM_spSafe v.impl (blkR v))
    features := v.impl.features },
  Spec.Gcm.streamDecryptPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 2584 1
      (Impl.AesGcm.X86_64.streamDecrypt (v.impl.withBlk (blkR v)))
    stack := 2608
    verified := Proof.AesGcm.streamDecryptPrepared_keyed (streamDecryptPrepared_framed v.impl (blkR v))
    spSafe := X86_64.withStackArgScratch_spSafe (streamDecryptM_spSafe v.impl (blkR v))
    features := v.impl.features }]

def artifactsGatherR (v : GcmVariant) : List Artifact :=
  [Spec.Gcm.sealGatherPreparedApi.artifact X86_64.target {
      suffix := v.impl.suffix
      code := Impl.StackScratch.X86_64.withStackArgScratch 240 5
        (Impl.AesGcm.X86_64.SealGather.withFront (tlsLong v) (splitFnR v).fn
          (Impl.AesGcm.X86_64.SealGather.sealGather (shortFnR v).quick (shortFnR v).fast (shortFnR v).test
            (shortFnR v).code (initFn v.impl).fn (aadFn v.impl).fn (toFnR v).fn (finFn v.impl).fn))
      stack := 5128
      verified := Proof.AesGcm.sealGatherPrepared_keyed (Gather.sealGatherPrepared_framed (shortFnR v) (initFn v.impl) (aadFn v.impl)
        (toFnR v) (finFn v.impl) (splitFnR v) (tlsLong v))
      spSafe := X86_64.withStackArgScratch_spSafe
        (Gather.withFront_spAll (shortFnR v) (initFn v.impl) (aadFn v.impl) (toFnR v)
          (finFn v.impl) (splitFnR v) (tlsLong v))
      features := v.impl.features }]

def artifactsR16 (v : GcmVariant) (r : R16 v) : List Artifact := [
  Spec.Gcm.sealPrepared16Api.artifact X86_64.target {
    suffix := v.impl.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 2600 3 (v.impl.sealCodeP (v.impl.withBlk (blkR16 v)))
    stack := 2624
    verified := Proof.AesGcm.sealPrepared16_keyed (sealSelPrepared16_framed v.impl (blkR16 v) Short.shortFacts r.short)
    spSafe := X86_64.withStackArgScratch_spSafe (sealCodeP_spSafe v.impl (blkR16 v))
    features := v.impl.features },
  Spec.Gcm.openPrepared16Api.artifact X86_64.target {
    suffix := v.impl.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 2608 4 (v.impl.openCodeP (v.impl.withBlk (blkR16 v)))
    stack := 2632
    verified := Proof.AesGcm.openPrepared16_keyed (openSelPrepared16_framed v.impl (blkR16 v) Short.shortFacts r.short)
    spSafe := X86_64.withStackArgScratch_spSafe (openCodeP_spSafe v.impl (blkR16 v))
    features := v.impl.features },
  Spec.Gcm.openToPrepared16Api.artifact X86_64.target {
    suffix := v.impl.suffix
    code := openToCodeR16 v r
    stack := openToStackR16 v
    verified := Proof.AesGcm.openToPrepared16_keyed (openToCodeR16_verified v r)
    spSafe := openToCodeR16_spAll v r
    features := v.impl.features },
  Spec.Gcm.streamEncryptPrepared16Api.artifact X86_64.target {
    suffix := v.impl.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 2584 1
      (Impl.AesGcm.X86_64.streamEncrypt (v.impl.withBlk (blkR16 v)))
    stack := 2608
    verified := Proof.AesGcm.streamEncryptPrepared16_keyed (streamEncryptPrepared16_framed v.impl (blkR16 v))
    spSafe := X86_64.withStackArgScratch_spSafe (streamEncryptM_spSafe v.impl (blkR16 v))
    features := v.impl.features },
  Spec.Gcm.streamDecryptPrepared16Api.artifact X86_64.target {
    suffix := v.impl.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 2584 1
      (Impl.AesGcm.X86_64.streamDecrypt (v.impl.withBlk (blkR16 v)))
    stack := 2608
    verified := Proof.AesGcm.streamDecryptPrepared16_keyed (streamDecryptPrepared16_framed v.impl (blkR16 v))
    spSafe := X86_64.withStackArgScratch_spSafe (streamDecryptM_spSafe v.impl (blkR16 v))
    features := v.impl.features }]

def artifactsGatherR16 (v : GcmVariant) (r : R16 v) : List Artifact :=
  [Spec.Gcm.sealGatherPrepared16Api.artifact X86_64.target {
      suffix := v.impl.suffix
      code := Impl.StackScratch.X86_64.withStackArgScratch 240 5
        (Impl.AesGcm.X86_64.SealGather.withFront (tlsLong v) (splitFnR16 v r.onePass).fn
          (Impl.AesGcm.X86_64.SealGather.sealGather (shortFnR16 v r.short r.onePass).quick (shortFnR16 v r.short r.onePass).fast (shortFnR16 v r.short r.onePass).test
            (shortFnR16 v r.short r.onePass).code (initFn v.impl).fn (aadFn v.impl).fn (toFnR16 v).fn (finFn v.impl).fn true))
      stack := 5128
      verified := Proof.AesGcm.sealGatherPrepared16_keyed (Gather.sealGatherPrepared16_framed (shortFnR16 v r.short r.onePass) (initFn v.impl) (aadFn v.impl)
        (toFnR16 v) (finFn v.impl) (splitFnR16 v r.onePass) (tlsLong v))
      spSafe := X86_64.withStackArgScratch_spSafe
        (Gather.withFront_spAll (shortFnR16 v r.short r.onePass) (initFn v.impl) (aadFn v.impl) (toFnR16 v)
          (finFn v.impl) (splitFnR16 v r.onePass) (tlsLong v) true)
      features := v.impl.features }]

/-- Artifacts propagate the context format supported by each variant: prepared
powers when available, otherwise raw precomputed powers. -/
def artifacts (v : GcmVariant) : List Artifact :=
  artifactsOf v.impl ++ (if v.impl.stitchP.isSome && v.stitchR.isNone then artifactsP v.impl else []) ++
    artifactsGather v ++
    (match v.r16 with
      | some r => artifactsR16 v r.down ++ artifactsGatherR16 v r.down
      | none => if v.stitchR.isSome then artifactsR v ++ artifactsGatherR v else [])

end VG.Generic.AesGcm.X86_64.AesGcm
