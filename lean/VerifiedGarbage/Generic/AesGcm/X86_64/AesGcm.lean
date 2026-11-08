module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Instances
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.X86_64.Registration
import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.Short
import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.Gather
import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.StreamTo
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
    features := v.features }]

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

/-- The prepared artifacts of the implementations `v` whose loops read the
48 prepared powers: by the flag, those or the ones on the key context. -/
def artifactsR (v : GcmVariant) : List Artifact := [
  Spec.Gcm.sealPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    code := Impl.Gcm.X86_64.Flag.onFlag
      (Impl.StackScratch.X86_64.withStackArgScratch 2600 3 (v.impl.sealCodeP (v.impl.withBlk (blkR v))))
      (Impl.StackScratch.X86_64.withStackArgScratch 2600 3 (v.impl.sealCode v.impl.callees))
    stack := 2624
    verified := VG.Proof.AesGcm.Flag.seal_keyed (Flag.seal_onFlag
      (sealSelPrepared_framed v.impl (blkR v) Short.shortFacts)
      (sealSel_framed v.impl Short.shortFacts))
    spSafe := VG.X86_64.onFlag_spSafe
      (X86_64.withStackArgScratch_spSafe (sealCodeP_spSafe v.impl (blkR v)))
      (X86_64.withStackArgScratch_spSafe (sealCode_spSafe v.impl v.impl.blkB))
    features := v.impl.features },
  Spec.Gcm.openPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    code := openCodeF v
    stack := 2632
    verified := VG.Proof.AesGcm.Flag.open_keyed (openCodeF_verified v)
    spSafe := openCodeF_spAll v
    features := v.impl.features },
  Spec.Gcm.openToPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    code := Impl.Gcm.X86_64.Flag.onFlag (openToCodeF v) (Impl.AesGcm.X86_64.OpenTo.openTo v.impl.copyW (openFn v.impl).fn)
    stack := openToStackR v
    verified := VG.Proof.AesGcm.Flag.openTo_keyed (openToCodeR_onFlag v)
    spSafe := VG.X86_64.onFlag_spSafe (openToCodeF_spAll v) (OpenTo.openTo_spAll v.impl.copyW _ (openFn v.impl).spAll)
    features := v.impl.features },
  Spec.Gcm.streamEncryptPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    code := Impl.Gcm.X86_64.Flag.onFlag
      (Impl.StackScratch.X86_64.withStackArgScratch 2584 1
      (Impl.AesGcm.X86_64.streamEncrypt (v.impl.withBlk (blkR v))))
      (Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncrypt v.impl.callees))
    stack := 2608
    verified := VG.Proof.AesGcm.Flag.streamEncrypt_keyed (Flag.streamEncrypt_onFlag
      (streamEncryptPrepared_framed v.impl (blkR v))
      (streamEncrypt_framed v.impl))
    spSafe := VG.X86_64.onFlag_spSafe
      (X86_64.withStackArgScratch_spSafe (streamEncryptM_spSafe v.impl (blkR v)))
      (X86_64.withStackArgScratch_spSafe (streamEncrypt_spSafe v.impl))
    features := v.impl.features },
  Spec.Gcm.streamDecryptPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    code := Impl.Gcm.X86_64.Flag.onFlag
      (Impl.StackScratch.X86_64.withStackArgScratch 2584 1
      (Impl.AesGcm.X86_64.streamDecrypt (v.impl.withBlk (blkR v))))
      (Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamDecrypt v.impl.callees))
    stack := 2608
    verified := VG.Proof.AesGcm.Flag.streamDecrypt_keyed (Flag.streamDecrypt_onFlag
      (streamDecryptPrepared_framed v.impl (blkR v))
      (streamDecrypt_framed v.impl))
    spSafe := VG.X86_64.onFlag_spSafe
      (X86_64.withStackArgScratch_spSafe (streamDecryptM_spSafe v.impl (blkR v)))
      (X86_64.withStackArgScratch_spSafe (streamDecrypt_spSafe v.impl))
    features := v.impl.features },
  Spec.Gcm.sealGatherPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    code := Impl.Gcm.X86_64.Flag.onFlag
      (Impl.StackScratch.X86_64.withStackArgScratch 240 5
        (Impl.AesGcm.X86_64.SealGather.withFront (tlsLong v) (splitFnR v).fn
          (Impl.AesGcm.X86_64.SealGather.sealGather (shortFnR v).quick (shortFnR v).fast (shortFnR v).test
            (shortFnR v).code (initFn v.impl).fn (aadFn v.impl).fn (toFnR v).fn (finFn v.impl).fn)))
      (Impl.StackScratch.X86_64.withStackArgScratch 240 5
        (Impl.AesGcm.X86_64.SealGather.sealGather (shortFn v).quick (shortFn v).fast (shortFn v).test
          (shortFn v).code (initFn v.impl).fn (aadFn v.impl).fn (toFn v).fn (finFn v.impl).fn))
    stack := 5128
    verified := VG.Proof.AesGcm.Flag.sealGather_keyed (Flag.sealGather_onFlag
      (Gather.sealGatherPrepared_framed (shortFnR v) (initFn v.impl) (aadFn v.impl)
        (toFnR v) (finFn v.impl) (splitFnR v) (tlsLong v))
      (Gather.sealGather_framed (shortFn v) (initFn v.impl) (aadFn v.impl) (toFn v) (finFn v.impl)))
    spSafe := VG.X86_64.onFlag_spSafe
      (X86_64.withStackArgScratch_spSafe
        (Gather.withFront_spAll (shortFnR v) (initFn v.impl) (aadFn v.impl) (toFnR v)
          (finFn v.impl) (splitFnR v) (tlsLong v)))
      (X86_64.withStackArgScratch_spSafe
        (Gather.sealGather_spAll (shortFn v) (initFn v.impl) (aadFn v.impl) (toFn v) (finFn v.impl)))
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

/-- The prepared artifacts of the implementations `v`, which read only the
key context. -/
def artifactsW (v : GcmVariant) : List Artifact := [
  Spec.Gcm.sealPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 2600 3 (v.impl.sealCode v.impl.callees)
    stack := 2624
    verified := VG.Proof.AesGcm.Flag.seal_keyed (Flag.seal_of_base (sealSel_framed v.impl Short.shortFacts))
    spSafe := X86_64.withStackArgScratch_spSafe (sealCode_spSafe v.impl v.impl.blkB)
    features := v.impl.features },
  Spec.Gcm.openPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 2608 4 (v.impl.openCode v.impl.callees)
    stack := 2632
    verified := VG.Proof.AesGcm.Flag.open_keyed (Flag.open_of_base (openSel_framed v.impl Short.shortFacts))
    spSafe := X86_64.withStackArgScratch_spSafe (openCode_spSafe v.impl v.impl.blkB)
    features := v.impl.features },
  Spec.Gcm.openToPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    code := Impl.AesGcm.X86_64.OpenTo.openTo v.impl.copyW (openFn v.impl).fn
    stack := 2728
    verified := VG.Proof.AesGcm.Flag.openTo_keyed (Flag.openTo_of_base (OpenTo.openTo_verified v.impl.copyW (openFn v.impl)))
    spSafe := OpenTo.openTo_spAll v.impl.copyW _ (openFn v.impl).spAll
    features := v.impl.features },
  Spec.Gcm.streamEncryptPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncrypt v.impl.callees)
    stack := 2608
    verified := VG.Proof.AesGcm.Flag.streamEncrypt_keyed (Flag.streamEncrypt_of_base (streamEncrypt_framed v.impl))
    spSafe := X86_64.withStackArgScratch_spSafe (streamEncrypt_spSafe v.impl)
    features := v.impl.features },
  Spec.Gcm.streamDecryptPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamDecrypt v.impl.callees)
    stack := 2608
    verified := VG.Proof.AesGcm.Flag.streamDecrypt_keyed (Flag.streamDecrypt_of_base (streamDecrypt_framed v.impl))
    spSafe := X86_64.withStackArgScratch_spSafe (streamDecrypt_spSafe v.impl)
    features := v.impl.features },
  Spec.Gcm.sealGatherPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 240 5
        (Impl.AesGcm.X86_64.SealGather.sealGather (shortFn v).quick (shortFn v).fast (shortFn v).test
          (shortFn v).code (initFn v.impl).fn (aadFn v.impl).fn (toFn v).fn (finFn v.impl).fn)
    stack := 5128
    verified := VG.Proof.AesGcm.Flag.sealGather_keyed (Flag.sealGather_of_base (Gather.sealGather_framed (shortFn v) (initFn v.impl) (aadFn v.impl) (toFn v) (finFn v.impl)))
    spSafe := X86_64.withStackArgScratch_spSafe
        (Gather.sealGather_spAll (shortFn v) (initFn v.impl) (aadFn v.impl) (toFn v) (finFn v.impl))
    features := v.impl.features }]

/-- The prepared artifacts of the implementations `v` whose loops read 16
prepared powers: by the flag, those or the ones on the key context. -/
def artifactsR16W (v : GcmVariant) (r : R16 v) : List Artifact := [
  Spec.Gcm.sealPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    code := Impl.Gcm.X86_64.Flag.onFlag
      (Impl.StackScratch.X86_64.withStackArgScratch 2600 3 (v.impl.sealCodeP (v.impl.withBlk (blkR16 v))))
      (Impl.StackScratch.X86_64.withStackArgScratch 2600 3 (v.impl.sealCode v.impl.callees))
    stack := 2624
    verified := VG.Proof.AesGcm.Flag.seal_keyed (Flag.seal_onFlag16
      (sealSelPrepared16_framed v.impl (blkR16 v) Short.shortFacts r.short)
      (sealSel_framed v.impl Short.shortFacts))
    spSafe := VG.X86_64.onFlag_spSafe
      (X86_64.withStackArgScratch_spSafe (sealCodeP_spSafe v.impl (blkR16 v)))
      (X86_64.withStackArgScratch_spSafe (sealCode_spSafe v.impl v.impl.blkB))
    features := v.impl.features },
  Spec.Gcm.openPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    code := Impl.Gcm.X86_64.Flag.onFlag
      (Impl.StackScratch.X86_64.withStackArgScratch 2608 4 (v.impl.openCodeP (v.impl.withBlk (blkR16 v))))
      (Impl.StackScratch.X86_64.withStackArgScratch 2608 4 (v.impl.openCode v.impl.callees))
    stack := 2632
    verified := VG.Proof.AesGcm.Flag.open_keyed (Flag.open_onFlag16
      (openSelPrepared16_framed v.impl (blkR16 v) Short.shortFacts r.short)
      (openSel_framed v.impl Short.shortFacts))
    spSafe := VG.X86_64.onFlag_spSafe
      (X86_64.withStackArgScratch_spSafe (openCodeP_spSafe v.impl (blkR16 v)))
      (X86_64.withStackArgScratch_spSafe (openCode_spSafe v.impl v.impl.blkB))
    features := v.impl.features },
  Spec.Gcm.openToPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    code := Impl.Gcm.X86_64.Flag.onFlag (openToCodeR16 v r) (Impl.AesGcm.X86_64.OpenTo.openTo v.impl.copyW (openFn v.impl).fn)
    stack := openToStackR16 v
    verified := VG.Proof.AesGcm.Flag.openTo_keyed (openToCodeR16_onFlag v r)
    spSafe := VG.X86_64.onFlag_spSafe (openToCodeR16_spAll v r) (OpenTo.openTo_spAll v.impl.copyW _ (openFn v.impl).spAll)
    features := v.impl.features },
  Spec.Gcm.streamEncryptPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    code := Impl.Gcm.X86_64.Flag.onFlag
      (Impl.StackScratch.X86_64.withStackArgScratch 2584 1
      (Impl.AesGcm.X86_64.streamEncrypt (v.impl.withBlk (blkR16 v))))
      (Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncrypt v.impl.callees))
    stack := 2608
    verified := VG.Proof.AesGcm.Flag.streamEncrypt_keyed (Flag.streamEncrypt_onFlag16
      (streamEncryptPrepared16_framed v.impl (blkR16 v))
      (streamEncrypt_framed v.impl))
    spSafe := VG.X86_64.onFlag_spSafe
      (X86_64.withStackArgScratch_spSafe (streamEncryptM_spSafe v.impl (blkR16 v)))
      (X86_64.withStackArgScratch_spSafe (streamEncrypt_spSafe v.impl))
    features := v.impl.features },
  Spec.Gcm.streamDecryptPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    code := Impl.Gcm.X86_64.Flag.onFlag
      (Impl.StackScratch.X86_64.withStackArgScratch 2584 1
      (Impl.AesGcm.X86_64.streamDecrypt (v.impl.withBlk (blkR16 v))))
      (Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamDecrypt v.impl.callees))
    stack := 2608
    verified := VG.Proof.AesGcm.Flag.streamDecrypt_keyed (Flag.streamDecrypt_onFlag16
      (streamDecryptPrepared16_framed v.impl (blkR16 v))
      (streamDecrypt_framed v.impl))
    spSafe := VG.X86_64.onFlag_spSafe
      (X86_64.withStackArgScratch_spSafe (streamDecryptM_spSafe v.impl (blkR16 v)))
      (X86_64.withStackArgScratch_spSafe (streamDecrypt_spSafe v.impl))
    features := v.impl.features },
  Spec.Gcm.sealGatherPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    code := Impl.Gcm.X86_64.Flag.onFlag
      (Impl.StackScratch.X86_64.withStackArgScratch 240 5
        (Impl.AesGcm.X86_64.SealGather.withFront (tlsLong v) (splitFnR16 v r.onePass).fn
          (Impl.AesGcm.X86_64.SealGather.sealGather (shortFnR16 v r.short r.onePass).quick
            (shortFnR16 v r.short r.onePass).fast (shortFnR16 v r.short r.onePass).test
            (shortFnR16 v r.short r.onePass).code (initFn v.impl).fn (aadFn v.impl).fn (toFnR16 v).fn
            (finFn v.impl).fn true)))
      (Impl.StackScratch.X86_64.withStackArgScratch 240 5
        (Impl.AesGcm.X86_64.SealGather.sealGather (shortFn v).quick (shortFn v).fast (shortFn v).test
          (shortFn v).code (initFn v.impl).fn (aadFn v.impl).fn (toFn v).fn (finFn v.impl).fn))
    stack := 5128
    verified := VG.Proof.AesGcm.Flag.sealGather_keyed (Flag.sealGather_onFlag16
      (Gather.sealGatherPrepared16_framed (shortFnR16 v r.short r.onePass) (initFn v.impl) (aadFn v.impl)
        (toFnR16 v) (finFn v.impl) (splitFnR16 v r.onePass) (tlsLong v))
      (Gather.sealGather_framed (shortFn v) (initFn v.impl) (aadFn v.impl) (toFn v) (finFn v.impl)))
    spSafe := VG.X86_64.onFlag_spSafe
      (X86_64.withStackArgScratch_spSafe
        (Gather.withFront_spAll (shortFnR16 v r.short r.onePass) (initFn v.impl) (aadFn v.impl) (toFnR16 v)
          (finFn v.impl) (splitFnR16 v r.onePass) (tlsLong v) true))
      (X86_64.withStackArgScratch_spSafe
        (Gather.sealGather_spAll (shortFn v) (initFn v.impl) (aadFn v.impl) (toFn v) (finFn v.impl)))
    features := v.impl.features }]

/-- The artifacts of a variant: those on the key context, and the prepared
ones of every variant. -/
def artifacts (v : GcmVariant) : List Artifact :=
  artifactsOf v.impl ++ (if v.impl.stitchP.isSome && v.stitchR.isNone then artifactsP v.impl else []) ++
    artifactsGather v ++
    (match v.r16 with
      | some r => artifactsR16 v r.down ++ artifactsGatherR16 v r.down ++ artifactsR16W v r.down
      | none => if v.stitchR.isSome then artifactsR v else artifactsW v)

end VG.Generic.AesGcm.X86_64.AesGcm
