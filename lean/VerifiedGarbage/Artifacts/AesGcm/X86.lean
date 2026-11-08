module

public import VerifiedGarbage.Proof.AesGcm.X86.GhashImpls
public import VerifiedGarbage.Proof.AesGcm.X86.Gather.Verified
public import VerifiedGarbage.Proof.AesGcm.X86.OpenTo.Verified
public import VerifiedGarbage.Proof.AesGcm.RoundsTo
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyRecurrence
public import VerifiedGarbage.Proof.Aes.X86.AesNi.Load
public import VerifiedGarbage.Proof.Aes.X86.AesNi.Prologue
public import VerifiedGarbage.Proof.Aes.X86.AesNi.Restore
public import VerifiedGarbage.Proof.Aes.X86.AesNi.Tail
public import VerifiedGarbage.Proof.AesGcm.X86.CryptHead
public import VerifiedGarbage.Proof.AesGcm.X86.CryptTail
public import VerifiedGarbage.Proof.AesGcm.X86.CryptWhole
public import VerifiedGarbage.Proof.AesGcm.X86.Flush
public import VerifiedGarbage.Proof.AesGcm.X86.Gather.CT
public import VerifiedGarbage.Proof.AesGcm.X86.Gather.Fn
public import VerifiedGarbage.Proof.AesGcm.X86.Init
public import VerifiedGarbage.Proof.Cmac.Frame
public import VerifiedGarbage.Proof.Cmac.Mem
public import VerifiedGarbage.Proof.Cmac.Spec
public import VerifiedGarbage.Proof.Framework.X86.SseTaint
public import VerifiedGarbage.Proof.Framework.X86.StackScratch
public import VerifiedGarbage.Proof.Gcm.SealGather
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.Variants.AesCtr32.X86
public import VerifiedGarbage.Proof.Variants.AesGcm.X86
public import VerifiedGarbage.Proof.Aes.X86.VariantProof
public import VerifiedGarbage.Proof.Variants.Ghash.X86

/-! # AES-GCM's AES-only function on x86: `vg_aes_gcm_init` -/

@[expose] public section

namespace VG.Artifacts.AesGcm.X86.AesCtr32

open VG.Proof.AesGcm.X86

/-- The artifacts calling the implementation `c` of `vg_aes_ctr32_to`, and no GHASH. -/
def artifacts (c : Proof.Aes.X86.Ctr32Impl) : List Artifact :=
  let v : GcmImpl := { ctr := c, gh := GhashName.scalar.impl }
  [
  Spec.Gcm.initApi.artifact X86.target {
    suffix := c.suffix
    code := Impl.StackScratch.X86.withStackScratch 2580 3 (Impl.AesGcm.X86.init v.callees)
    stack := 2612
    verified := init_framed v
    spSafe := withStackScratch_spSafe (init_spSafe v)
    features := (v.ctr.features) }]

end VG.Artifacts.AesGcm.X86.AesCtr32

-- AES-GCM (NIST SP 800-38D) on x86
namespace VG.Artifacts.AesGcm.X86.AesGcm

open VG.Proof.AesGcm.X86

/-- The artifacts calling the implementations `v`. -/
def artifactsOf (v : GcmImpl) : List Artifact := [
  Spec.Gcm.streamEncryptApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86.withStackScratch 2604 9 (Impl.AesGcm.X86.streamEncrypt v.callees)
    stack := 2636
    verified := Proof.AesGcm.streamEncrypt_keyed (streamEncrypt_framed v)
    spSafe := withStackScratch_spSafe (streamEncrypt_spSafe v)
    features := v.features },
  Spec.Gcm.streamDecryptApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86.withStackScratch 2604 9 (Impl.AesGcm.X86.streamDecrypt v.callees)
    stack := 2636
    verified := Proof.AesGcm.streamDecrypt_keyed (streamDecrypt_framed v)
    spSafe := withStackScratch_spSafe (streamDecrypt_spSafe v)
    features := v.features },
  Spec.Gcm.streamFinishApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86.withStackScratch 2600 8 (Impl.AesGcm.X86.streamFinish v.callees)
    stack := 2632
    verified := Proof.AesGcm.streamFinish_keyed (streamFinish_framed v)
    spSafe := withStackScratch_spSafe (streamFinish_spSafe v)
    features := v.features },
  Spec.Gcm.streamVerifyApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86.withStackScratch 2604 9 (Impl.AesGcm.X86.streamVerify v.callees)
    stack := 2636
    verified := Proof.AesGcm.streamVerify_keyed (streamVerify_framed v)
    spSafe := withStackScratch_spSafe (streamVerify_spSafe v)
    features := v.features },
  Spec.Gcm.sealApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86.withStackScratch 2604 9 (Impl.AesGcm.X86.«seal» v.callees)
    stack := 2636
    verified := Proof.AesGcm.seal_keyed (seal_framed v)
    spSafe := withStackScratch_spSafe (seal_spSafe v)
    features := v.features },
  Spec.Gcm.openApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86.withStackScratch 2608 10 (Impl.AesGcm.X86.«open» v.callees)
    stack := 2640
    verified := Proof.AesGcm.open_keyed (open_framed v)
    spSafe := withStackScratch_spSafe (open_spSafe v)
    features := v.features }]

/-- `vg_aes_gcm_seal_gather`, calling the instance of `vg_aes_gcm_seal` of the implementations `v`. -/
def artifactsGather (v : GcmImpl) : List Artifact := [
  Spec.Gcm.sealGatherApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.AesGcm.X86.SealGather.sealGather (Gather.sealFn v).name (Gather.sealFn v).code
    stack := 2688
    verified := Proof.AesGcm.sealGather_keyed (Gather.sealGather_verified (Gather.sealFn v))
    spSafe := Gather.sealGather_spSafe v
    features := v.features }]

/-- `vg_aes_gcm_open_to`, calling `vg_aes_ctr32_to` of the implementations `v`. -/
def artifactsOpenTo (v : GcmImpl) : List Artifact := [
  Spec.Gcm.openToApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86.withStackScratch 2616 12 (Impl.AesGcm.X86.Open.openTo v.callees (OpenTo.toFn v))
    stack := 2696
    verified := Proof.AesGcm.openTo_keyed (OpenTo.openTo_framed v)
    spSafe := OpenTo.openTo_spSafe v
    features := v.features }]

/-- The artifacts of a variant, from the implementations it names. -/
def artifacts (v : GcmVariant) : List Artifact :=
  artifactsOf v.impl ++ artifactsGather v.impl ++ artifactsOpenTo v.impl

end VG.Artifacts.AesGcm.X86.AesGcm

-- AES-GCM's GHASH-only functions on x86
namespace VG.Artifacts.AesGcm.X86.Ghash

open VG.Proof.AesGcm.X86

/-- The artifacts calling the implementation `n` of `vg_ghash`, and no AES. -/
def artifacts (n : GhashName) : List Artifact :=
  let v : GcmImpl := { ctr := Proof.Aes.X86.Ctr32Impl.scalar, gh := n.impl }
  [
  Spec.Gcm.streamAadApi.artifact X86.target {
    suffix := n.impl.suffix
    code := Impl.StackScratch.X86.withStackScratch 2592 6 (Impl.AesGcm.X86.streamAad v.callees)
    stack := 2616
    verified := streamAad_framed v
    spSafe := withStackScratch_spSafe (streamAad_spSafe v)
    features := v.gh.features },
  Spec.Gcm.streamInitApi.artifact X86.target {
    suffix := n.impl.suffix
    code := Impl.StackScratch.X86.withStackScratch 2584 4 (Impl.AesGcm.X86.streamInit v.callees)
    stack := 2608
    verified := streamInit_framed v
    spSafe := withStackScratch_spSafe (streamInit_spSafe v)
    features := v.gh.features }]

end VG.Artifacts.AesGcm.X86.Ghash

namespace VG.Artifacts.AesGcm.X86

def artifacts : List Artifact :=
  (VG.Proof.Variants.AesCtr32.X86.variants.flatMap fun v => AesCtr32.artifacts v) ++
  (VG.Proof.Variants.AesGcm.X86.variants.flatMap fun v => AesGcm.artifacts v) ++
  (VG.Proof.Variants.Ghash.X86.variants.flatMap fun v => Ghash.artifacts v)

end VG.Artifacts.AesGcm.X86
