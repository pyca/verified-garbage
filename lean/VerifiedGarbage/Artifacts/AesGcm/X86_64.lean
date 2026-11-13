module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Instances
public import VerifiedGarbage.Proof.Aes.X86_64.Variant
public import VerifiedGarbage.Proof.AesGcm.X86_64.GhashImpls
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
public import VerifiedGarbage.TCB.X86_64.Print
public import VerifiedGarbage.Proof.Variants.AesCtr32.X86_64
public import VerifiedGarbage.Proof.Variants.Ghash.X86_64
public import VerifiedGarbage.Proof.Gcm.X86_64.PrepareScrub
public import VerifiedGarbage.Proof.AesGcm.X86_64.Scrub
import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.Short
import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.Gather
import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.StreamTo
import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.Verified
import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.BlocksVerified
import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksVerifiedP
public import VerifiedGarbage.Proof.Variants.AesGcm.X86_64
import VerifiedGarbage.Proof.Gcm.X86_64.Vpclmul.Lit
import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Lit
import VerifiedGarbage.Proof.Gcm.X86_64.Lit
public import VerifiedGarbage.Proof.Gcm.X86_64.Ghash
public import VerifiedGarbage.Proof.Gcm.X86_64.Vpclmul.Ghash
public import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Ok
public import VerifiedGarbage.Proof.Gcm.X86_64.PrepareZ
public import VerifiedGarbage.Proof.Gcm.X86_64.PrepareAvx.Ok
public import VerifiedGarbage.Proof.Gcm.X86_64.Prepare16

/-! # AES-GCM (NIST SP 800-38D) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.AesGcm.X86_64.AesCtr32Ghash

open VG.Proof.AesGcm.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)

/-- The artifacts calling the implementation `c` of `vg_aes_ctr32` and `n` of
`vg_ghash`, a pair that a variant of AES-GCM calls (`streamPairs`). -/
def artifacts (c : Ctr32Impl) (n : GhashName) : List Artifact :=
  let v : GcmImpl :=
    { ctr := c, key := if c.features.isEmpty then KeyImpl.scalar else KeyImpl.aesni,
      gh := n.impl }
  [
  Spec.Gcm.streamFinishApi.artifact X86_64.target {
    suffix := c.suffix ++ n.impl.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 2576 0 (Impl.AesGcm.X86_64.streamFinish v.callees)
    stack := 2584
    verified := Proof.AesGcm.streamFinish_keyed (streamFinish_framed v)
    spSafe := X86_64.withStackArgScratch_spSafe (streamFinish_spSafe v) },
  Spec.Gcm.streamVerifyApi.artifact X86_64.target {
    suffix := c.suffix ++ n.impl.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamVerify v.callees)
    stack := 2592
    verified := Proof.AesGcm.streamVerify_keyed (streamVerify_framed v)
    spSafe := X86_64.withStackArgScratch_spSafe (streamVerify_spSafe v) }]

end VG.Artifacts.AesGcm.X86_64.AesCtr32Ghash

-- AES-GCM's AES-only function on x86-64: `vg_aes_gcm_init`
namespace VG.Artifacts.AesGcm.X86_64.AesCtr32

open VG.Proof.AesGcm.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)

/-- The artifacts calling the implementation `c` of `vg_aes_ctr32`, with the
key expansion for the same CPUs, and no GHASH. -/
def artifacts (c : Ctr32Impl) : List Artifact :=
  [Spec.Gcm.initApi.artifact X86_64.target (Proof.AesGcm.X86_64.Scrub.initReg c)]

end VG.Artifacts.AesGcm.X86_64.AesCtr32

-- AES-GCM (NIST SP 800-38D) on x86-64
namespace VG.Artifacts.AesGcm.X86_64.AesGcm

open VG.Proof.AesGcm.X86_64

/-- The prepared artifacts of the implementations `v` whose loops read the
48 prepared powers: by the flag, those or the ones on the key context. -/
def artifactsR (v : GcmVariant) : List Artifact := [
  Spec.Gcm.sealPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    code := sealCodeF v
    stack := 2624
    verified := VG.Proof.AesGcm.Flag.seal_keyed (Flag.seal_ofB (Or.inr rfl) (sealCodeF_verified v))
    spSafe := sealCodeF_spAll v },
  Spec.Gcm.openPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    code := openCodeF v
    stack := 2632
    verified := VG.Proof.AesGcm.Flag.open_keyed (Flag.open_ofB (Or.inr rfl) (openCodeF_verified v))
    spSafe := openCodeF_spAll v },
  Spec.Gcm.openToPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    code := Impl.Gcm.X86_64.Flag.onFlag 48 (openToCodeF v) (openToCode v)
    stack := openToStackF v
    verified := VG.Proof.AesGcm.Flag.openTo_keyed (openToCodeR_onFlag v)
    spSafe := openToCodeR_onFlag_spAll v },
  Spec.Gcm.streamEncryptPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    code := streamEncryptCodeF v
    stack := 2608
    verified := VG.Proof.AesGcm.Flag.streamEncrypt_keyed (Flag.streamEncrypt_ofB (Or.inr rfl) (streamEncryptCodeF_verified v))
    spSafe := streamEncryptCodeF_spAll v },
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
      (X86_64.withStackArgScratch_spSafe (streamDecrypt_spSafe v.impl)) },
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
        (Gather.sealGather_spAll (shortFn v) (initFn v.impl) (aadFn v.impl) (toFn v) (finFn v.impl))) }]

/-- The prepared artifacts of the implementations `v`, which read only the
key context. -/
def artifactsW (v : GcmVariant) : List Artifact := [
  Spec.Gcm.sealPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 2600 3 (v.impl.sealCode v.impl.callees)
    stack := 2624
    verified := VG.Proof.AesGcm.Flag.seal_keyed (Flag.seal_of_base (sealSel_framed v.impl Short.shortFacts))
    spSafe := X86_64.withStackArgScratch_spSafe (sealCode_spSafe v.impl v.impl.blkB) },
  Spec.Gcm.openPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 2608 4 (v.impl.openCode v.impl.callees)
    stack := 2632
    verified := VG.Proof.AesGcm.Flag.open_keyed (Flag.open_of_base (openSel_framed v.impl Short.shortFacts))
    spSafe := X86_64.withStackArgScratch_spSafe (openCode_spSafe v.impl v.impl.blkB) },
  Spec.Gcm.openToPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    code := openToCode v
    stack := openToStack v
    verified := VG.Proof.AesGcm.Flag.openTo_keyed (openToCode_keyed v)
    spSafe := openToCode_spAll v },
  Spec.Gcm.streamEncryptPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncrypt v.impl.callees)
    stack := 2608
    verified := VG.Proof.AesGcm.Flag.streamEncrypt_keyed (Flag.streamEncrypt_of_base (streamEncrypt_framed v.impl))
    spSafe := X86_64.withStackArgScratch_spSafe (streamEncrypt_spSafe v.impl) },
  Spec.Gcm.streamDecryptPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamDecrypt v.impl.callees)
    stack := 2608
    verified := VG.Proof.AesGcm.Flag.streamDecrypt_keyed (Flag.streamDecrypt_of_base (streamDecrypt_framed v.impl))
    spSafe := X86_64.withStackArgScratch_spSafe (streamDecrypt_spSafe v.impl) },
  Spec.Gcm.sealGatherPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 240 5
        (Impl.AesGcm.X86_64.SealGather.sealGather (shortFn v).quick (shortFn v).fast (shortFn v).test
          (shortFn v).code (initFn v.impl).fn (aadFn v.impl).fn (toFn v).fn (finFn v.impl).fn)
    stack := 5128
    verified := VG.Proof.AesGcm.Flag.sealGather_keyed (Flag.sealGather_of_base (Gather.sealGather_framed (shortFn v) (initFn v.impl) (aadFn v.impl) (toFn v) (finFn v.impl)))
    spSafe := X86_64.withStackArgScratch_spSafe
        (Gather.sealGather_spAll (shortFn v) (initFn v.impl) (aadFn v.impl) (toFn v) (finFn v.impl)) }]

/-- The prepared artifacts of the implementations `v` whose loops read 16
prepared powers: by the count, those or the ones on the key context. -/
def artifactsR16W (v : GcmVariant) (r : R16 v) : List Artifact := [
  Spec.Gcm.sealPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    code := sealCodeF16 v
    stack := 2624
    verified := VG.Proof.AesGcm.Flag.seal_keyed (Flag.seal_ofB (Or.inl rfl) (sealCodeF16_verified v r))
    spSafe := sealCodeF16_spAll v },
  Spec.Gcm.openPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    code := openCodeF16 v
    stack := 2632
    verified := VG.Proof.AesGcm.Flag.open_keyed (Flag.open_ofB (Or.inl rfl) (openCodeF16_verified v r))
    spSafe := openCodeF16_spAll v },
  Spec.Gcm.openToPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    code := Impl.Gcm.X86_64.Flag.onFlag 16 (openToCodeF16 v r) (openToCode v)
    stack := openToStackF16 v
    verified := VG.Proof.AesGcm.Flag.openTo_keyed (openToCodeR16_onFlag v r)
    spSafe := openToCodeR16_onFlag_spAll v r },
  Spec.Gcm.streamEncryptPreparedApi.artifact X86_64.target {
    suffix := v.impl.suffix
    code := streamEncryptCodeF16 v
    stack := 2608
    verified := VG.Proof.AesGcm.Flag.streamEncrypt_keyed
      (Flag.streamEncrypt_ofB (Or.inl rfl) (streamEncryptCodeF16_verified v))
    spSafe := streamEncryptCodeF16_spAll v },
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
      (X86_64.withStackArgScratch_spSafe (streamDecrypt_spSafe v.impl)) },
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
        (Gather.sealGather_spAll (shortFn v) (initFn v.impl) (aadFn v.impl) (toFn v) (finFn v.impl))) }]

/-- The artifacts of a variant: its prepared ones, for what its loops read:
16 prepared powers (`r16`), 48 (`stitchR`), or the key context alone. -/
def artifacts (v : GcmVariant) : List Artifact :=
  match v.r16 with
  | some r => artifactsR16W v r.down
  | none => if v.stitchR.isSome then artifactsR v else artifactsW v

end VG.Artifacts.AesGcm.X86_64.AesGcm

-- AES-GCM's GHASH-only functions on x86-64
namespace VG.Artifacts.AesGcm.X86_64.Ghash

open VG.Proof.AesGcm.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)

/-- The artifacts calling the implementation `n` of `vg_ghash`, and no AES. -/
def artifacts (n : GhashName) : List Artifact :=
  let v : GcmImpl := { ctr := Ctr32Impl.scalar, key := KeyImpl.scalar, gh := n.impl }
  [
  Spec.Gcm.streamInitApi.artifact X86_64.target {
    suffix := n.impl.suffix
    code := Impl.StackScratch.X86_64.withStackScratch 2568 .r8
      (Impl.AesGcm.X86_64.streamInit v.callees)
    stack := 2576
    verified := streamInit_framed v
    spSafe := X86_64.withStackScratch_spSafe_of (streamInit_spSafe v) },
  Spec.Gcm.streamAadApi.artifact X86_64.target {
    suffix := n.impl.suffix
    code := Impl.StackScratch.X86_64.withStackScratch 2568 .r9
      (Impl.AesGcm.X86_64.streamAad v.callees)
    stack := 2576
    verified := streamAad_framed v
    spSafe := X86_64.withStackScratch_spSafe_of (streamAad_spSafe v) }]

end VG.Artifacts.AesGcm.X86_64.Ghash

namespace VG.Artifacts.AesGcm.X86_64

def artifacts : List Artifact :=
  ((Proof.AesGcm.X86_64.streamPairs VG.Proof.Variants.AesGcm.X86_64.variants).flatMap fun (c, n) =>
    AesCtr32Ghash.artifacts c n) ++
  (VG.Proof.Variants.AesCtr32.X86_64.variants.flatMap fun v => AesCtr32.artifacts v) ++
  (VG.Proof.Variants.AesGcm.X86_64.variants.flatMap fun v => AesGcm.artifacts v) ++
  (VG.Proof.Variants.Ghash.X86_64.variants.flatMap fun v => Ghash.artifacts v) ++
  [
    Spec.Gcm.prepareApi.artifact X86_64.target Proof.Gcm.X86_64.PrepareScrub.zReg,
    Spec.Gcm.prepareApi.artifact X86_64.target Proof.Gcm.X86_64.PrepareScrub.p16Reg,
    Spec.Gcm.prepareApi.artifact X86_64.target Proof.Gcm.X86_64.PrepareScrub.avxReg,
    Spec.Gcm.prepareApi.artifact X86_64.target Proof.Gcm.X86_64.PrepareScrub.absentReg,
    Spec.Gcm.wipePreparedApi.artifact X86_64.target (Proof.Gcm.X86_64.PrepareScrub.wipeReg true),
    Spec.Gcm.wipePreparedApi.artifact X86_64.target (Proof.Gcm.X86_64.PrepareScrub.wipeReg false)]

end VG.Artifacts.AesGcm.X86_64
