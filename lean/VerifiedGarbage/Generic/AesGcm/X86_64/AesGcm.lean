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

/-- The prepared artifacts of the implementations `v` whose loops read the
48 prepared powers: by the flag, those or the ones on the key context. -/
def artifactsR (v : GcmVariant) : List Artifact := [
  Spec.Gcm.sealPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    code := sealCodeF v
    stack := 2624
    verified := VG.Proof.AesGcm.Flag.seal_keyed (Flag.seal_ofB (Or.inr rfl) (sealCodeF_verified v))
    spSafe := sealCodeF_spAll v
    features := v.impl.features },
  Spec.Gcm.openPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    code := openCodeF v
    stack := 2632
    verified := VG.Proof.AesGcm.Flag.open_keyed (Flag.open_ofB (Or.inr rfl) (openCodeF_verified v))
    spSafe := openCodeF_spAll v
    features := v.impl.features },
  Spec.Gcm.openToPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    code := Impl.Gcm.X86_64.Flag.onFlag 48 (openToCodeF v) (openToCode v)
    stack := openToStackF v
    verified := VG.Proof.AesGcm.Flag.openTo_keyed (openToCodeR_onFlag v)
    spSafe := openToCodeR_onFlag_spAll v
    features := v.impl.features },
  Spec.Gcm.streamEncryptPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    code := streamEncryptCodeF v
    stack := 2608
    verified := VG.Proof.AesGcm.Flag.streamEncrypt_keyed (Flag.streamEncrypt_ofB (Or.inr rfl) (streamEncryptCodeF_verified v))
    spSafe := streamEncryptCodeF_spAll v
    features := v.impl.features },
  Spec.Gcm.streamDecryptPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    code := Impl.Gcm.X86_64.Flag.onFlag 48
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
    code := Impl.Gcm.X86_64.Flag.onFlag 48 (sealGatherCodeF v)
      (Impl.StackScratch.X86_64.withStackArgScratch 240 5
        (Impl.AesGcm.X86_64.SealGather.sealGather (shortFn v).quick (shortFn v).fast (shortFn v).test
          (shortFn v).code (initFn v.impl).fn (aadFn v.impl).fn (toFn v).fn (finFn v.impl).fn))
    stack := 5128
    verified := VG.Proof.AesGcm.Flag.sealGather_keyed (sealGatherR_onFlag v)
    spSafe := VG.X86_64.onFlag_spSafe (sealGatherCodeF_spAll v)
      (X86_64.withStackArgScratch_spSafe
        (Gather.sealGather_spAll (shortFn v) (initFn v.impl) (aadFn v.impl) (toFn v) (finFn v.impl)))
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
    code := openToCode v
    stack := openToStack v
    verified := VG.Proof.AesGcm.Flag.openTo_keyed (openToCode_keyed v)
    spSafe := openToCode_spAll v
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
prepared powers: by the count, those or the ones on the key context. -/
def artifactsR16W (v : GcmVariant) (r : R16 v) : List Artifact := [
  Spec.Gcm.sealPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    code := sealCodeF16 v
    stack := 2624
    verified := VG.Proof.AesGcm.Flag.seal_keyed (Flag.seal_ofB (Or.inl rfl) (sealCodeF16_verified v r))
    spSafe := sealCodeF16_spAll v
    features := v.impl.features },
  Spec.Gcm.openPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    code := openCodeF16 v
    stack := 2632
    verified := VG.Proof.AesGcm.Flag.open_keyed (Flag.open_ofB (Or.inl rfl) (openCodeF16_verified v r))
    spSafe := openCodeF16_spAll v
    features := v.impl.features },
  Spec.Gcm.openToPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    code := Impl.Gcm.X86_64.Flag.onFlag 16 (openToCodeF16 v r) (openToCode v)
    stack := openToStackF16 v
    verified := VG.Proof.AesGcm.Flag.openTo_keyed (openToCodeR16_onFlag v r)
    spSafe := openToCodeR16_onFlag_spAll v r
    features := v.impl.features },
  Spec.Gcm.streamEncryptPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    code := streamEncryptCodeF16 v
    stack := 2608
    verified := VG.Proof.AesGcm.Flag.streamEncrypt_keyed
      (Flag.streamEncrypt_ofB (Or.inl rfl) (streamEncryptCodeF16_verified v))
    spSafe := streamEncryptCodeF16_spAll v
    features := v.impl.features },
  Spec.Gcm.streamDecryptPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    code := Impl.Gcm.X86_64.Flag.onFlag 16
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
    code := Impl.Gcm.X86_64.Flag.onFlag 16 (sealGatherCodeF16 v r)
      (Impl.StackScratch.X86_64.withStackArgScratch 240 5
        (Impl.AesGcm.X86_64.SealGather.sealGather (shortFn v).quick (shortFn v).fast (shortFn v).test
          (shortFn v).code (initFn v.impl).fn (aadFn v.impl).fn (toFn v).fn (finFn v.impl).fn))
    stack := 5128
    verified := VG.Proof.AesGcm.Flag.sealGather_keyed (sealGatherR16_onFlag v r)
    spSafe := VG.X86_64.onFlag_spSafe (sealGatherCodeF16_spAll v r)
      (X86_64.withStackArgScratch_spSafe
        (Gather.sealGather_spAll (shortFn v) (initFn v.impl) (aadFn v.impl) (toFn v) (finFn v.impl)))
    features := v.impl.features }]

/-- The artifacts of a variant: its prepared ones. -/
def artifacts (v : GcmVariant) : List Artifact :=
  match v.r16 with
  | some r => artifactsR16W v r.down
  | none => if v.stitchR.isSome then artifactsR v else artifactsW v

end VG.Generic.AesGcm.X86_64.AesGcm
