module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Gcm.Contract
public import VerifiedGarbage.Spec.Gcm.Contiguous
public import VerifiedGarbage.Spec.Gcm.OutOfPlace
import VerifiedGarbage.Proof.AesGcm.X86.Contiguous.Scrub
import VerifiedGarbage.Proof.AesGcm.X86.GhashImpls
import VerifiedGarbage.Proof.AesGcm.X86.Scrub
import VerifiedGarbage.Impl.AesGcm.X86.Fn
import VerifiedGarbage.Proof.AesGcm.X86.Gather.Verified
import VerifiedGarbage.Proof.AesGcm.X86.OpenTo.Verified
import VerifiedGarbage.Proof.AesGcm.RoundsTo
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyRecurrence
import VerifiedGarbage.Proof.Aes.X86.AesNi.Load
import VerifiedGarbage.Proof.Aes.X86.AesNi.Prologue
import VerifiedGarbage.Proof.Aes.X86.AesNi.Restore
import VerifiedGarbage.Proof.Aes.X86.AesNi.Tail
import VerifiedGarbage.Proof.AesGcm.X86.CryptHead
import VerifiedGarbage.Proof.AesGcm.X86.CryptTail
import VerifiedGarbage.Proof.AesGcm.X86.CryptWhole
import VerifiedGarbage.Proof.AesGcm.X86.Flush
import VerifiedGarbage.Proof.AesGcm.X86.Gather.Fn
import VerifiedGarbage.Proof.AesGcm.X86.Init
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.X86.StackScratch
import VerifiedGarbage.Proof.Gcm.SealGather
import VerifiedGarbage.Proof.Variants.AesCtr32.X86
import VerifiedGarbage.Proof.Variants.AesGcm.X86
import VerifiedGarbage.Proof.Aes.X86.VariantProof
import VerifiedGarbage.Proof.Variants.Ghash.X86
import VerifiedGarbage.Proof.Framework.SpecApis


/-! # AES-GCM (NIST SP 800-38D) on x86 -/

namespace VG.Artifacts.AesGcm.X86.AesCtr32

open VG.Proof.AesGcm.X86 VG.Proof.AesGcm.X86.Scrub

/-- The artifacts calling the implementation `c` of `vg_aes_ctr32_to`, and no GHASH. -/
def artifacts (c : Proof.Aes.X86.Ctr32Impl) : List (Artifact X86.target) :=
  let v : GcmImpl := { ctr := c, gh := GhashName.scalar.impl }
  [
  Spec.Gcm.initApi.artifact X86.target {
    suffix := c.suffix
    code := Impl.AesGcm.X86.Fn.init v.callees
    verified := Proof.AesGcm.X86.Scrub.init_scrubbed v
    spSafe := Proof.AesGcm.X86.Scrub.init_spSafeF v }]

end VG.Artifacts.AesGcm.X86.AesCtr32

-- AES-GCM (NIST SP 800-38D) on x86
namespace VG.Artifacts.AesGcm.X86.AesGcm

open VG.Proof.AesGcm.X86 VG.Proof.AesGcm.X86.Scrub

/-- The artifacts calling the implementations `v`. -/
def artifactsOf (v : GcmImpl) : List (Artifact X86.target) := [
  Spec.Gcm.streamEncryptApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.AesGcm.X86.Fn.streamEncrypt v.callees
    verified := Proof.AesGcm.X86.Scrub.streamEncrypt_scrubbed v
    spSafe := Proof.AesGcm.X86.Scrub.streamEncrypt_spSafeF v },
  Spec.Gcm.streamDecryptApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.AesGcm.X86.Fn.streamDecrypt v.callees
    verified := Proof.AesGcm.X86.Scrub.streamDecrypt_scrubbed v
    spSafe := Proof.AesGcm.X86.Scrub.streamDecrypt_spSafeF v },
  Spec.Gcm.streamFinishApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.AesGcm.X86.Fn.streamFinish v.callees
    verified := Proof.AesGcm.X86.Scrub.streamFinish_scrubbed v
    spSafe := Proof.AesGcm.X86.Scrub.streamFinish_spSafeF v },
  Spec.Gcm.streamVerifyApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.AesGcm.X86.Fn.streamVerify v.callees
    verified := Proof.AesGcm.X86.Scrub.streamVerify_scrubbed v
    spSafe := Proof.AesGcm.X86.Scrub.streamVerify_spSafeF v },
  Spec.Gcm.sealApi.artifact X86.target
    (if h : v.ctr.scr ≤ 256 then
      { suffix := v.suffix
        code := Impl.AesGcm.X86.Fn.«seal» v.callees 96
        verified := Proof.AesGcm.X86.Scrub.sealS_scrubbed v h
        spSafe := Proof.AesGcm.X86.Scrub.sealS_spSafeF v }
    else
      { suffix := v.suffix
        code := Impl.AesGcm.X86.Fn.«seal» v.callees 320
        verified := Proof.AesGcm.X86.Scrub.seal_scrubbed v
        spSafe := Proof.AesGcm.X86.Scrub.seal_spSafeF v }),
  Spec.Gcm.openApi.artifact X86.target
    (if h : v.ctr.scr ≤ 256 then
      { suffix := v.suffix
        code := Impl.AesGcm.X86.Fn.«open» v.callees 96
        verified := Proof.AesGcm.X86.Scrub.openS_scrubbed v h
        spSafe := Proof.AesGcm.X86.Scrub.openS_spSafeF v }
    else
      { suffix := v.suffix
        code := Impl.AesGcm.X86.Fn.«open» v.callees 320
        verified := Proof.AesGcm.X86.Scrub.open_scrubbed v
        spSafe := Proof.AesGcm.X86.Scrub.open_spSafeF v })]

/-- Gather seal reads plaintext descriptors directly into the ciphertext destination. -/
def artifactsGather (v : GcmImpl) : List (Artifact X86.target) := [
  (letI := Impl.AesGcm.X86.Contiguous.FrameSize.forScratch v.ctr.scr
   letI := Proof.AesGcm.X86.Contiguous.sizeFor v
   Spec.Gcm.sealContiguousApi.artifact X86.target {
     suffix := v.suffix
     code := Impl.AesGcm.X86.Contiguous.scrubbed v.callees
     verified := Proof.AesGcm.X86.Contiguous.verifiedScrub v
     spSafe := Proof.AesGcm.X86.Contiguous.scrubbedSafe v }),
  Spec.Gcm.sealGatherApi.artifact X86.target
    (if h : v.ctr.scr ≤ 256 then
      { suffix := v.suffix
        code := Impl.AesGcm.X86.Fn.sealGather v.callees 96
        verified := Proof.AesGcm.X86.Scrub.sealGatherS_scrubbed v h
        spSafe := Proof.AesGcm.X86.Scrub.sealGatherS_spSafeF v }
    else
      { suffix := v.suffix
        code := Impl.AesGcm.X86.Fn.sealGather v.callees 320
        verified := Proof.AesGcm.X86.Scrub.sealGather_scrubbed v
        spSafe := Proof.AesGcm.X86.Scrub.sealGather_spSafeF v })]

/-- `vg_aes_gcm_open_to`, calling `vg_aes_ctr32_to` of the implementations `v`. -/
def artifactsOpenTo (v : GcmImpl) : List (Artifact X86.target) := [
  Spec.Gcm.openToApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.AesGcm.X86.Fn.openTo v.callees (OpenTo.toFn v)
    verified := Proof.AesGcm.X86.Scrub.openTo_scrubbed v
    spSafe := Proof.AesGcm.X86.Scrub.openTo_spSafeF v }]

/-- The artifacts of a variant, from the implementations it names. -/
def artifacts (v : GcmVariant) : List (Artifact X86.target) :=
  artifactsOf v.impl ++ artifactsGather v.impl ++ artifactsOpenTo v.impl

end VG.Artifacts.AesGcm.X86.AesGcm

-- AES-GCM's GHASH-only functions on x86
namespace VG.Artifacts.AesGcm.X86.Ghash

open VG.Proof.AesGcm.X86 VG.Proof.AesGcm.X86.Scrub

/-- The artifacts calling the implementation `n` of `vg_ghash`, and no AES. -/
def artifacts (n : GhashName) : List (Artifact X86.target) :=
  let v : GcmImpl := { ctr := Proof.Aes.X86.Ctr32Impl.scalar, gh := n.impl }
  [
  Spec.Gcm.streamAadApi.artifact X86.target {
    suffix := n.impl.suffix
    code := Impl.AesGcm.X86.Fn.streamAad v.callees
    verified := Proof.AesGcm.X86.Scrub.streamAad_scrubbed v
    spSafe := Proof.AesGcm.X86.Scrub.streamAad_spSafeF v },
  Spec.Gcm.streamInitApi.artifact X86.target {
    suffix := n.impl.suffix
    code := Impl.AesGcm.X86.Fn.streamInit v.callees
    verified := Proof.AesGcm.X86.Scrub.streamInit_scrubbed v
    spSafe := Proof.AesGcm.X86.Scrub.streamInit_spSafeF v }]

end VG.Artifacts.AesGcm.X86.Ghash

namespace VG.Artifacts.AesGcm.X86

public def artifacts : List (Artifact X86.target) :=
  (VG.Proof.Variants.AesCtr32.X86.variants.flatMap fun v => AesCtr32.artifacts v) ++
  (VG.Proof.Variants.AesGcm.X86.variants.flatMap fun v => AesGcm.artifacts v) ++
  (VG.Proof.Variants.Ghash.X86.variants.flatMap fun v => Ghash.artifacts v)

spec_apis artifacts

end VG.Artifacts.AesGcm.X86
