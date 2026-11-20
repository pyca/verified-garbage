module

public import VerifiedGarbage.Proof.AesGcm.X86.GhashImpls
public import VerifiedGarbage.Proof.AesGcm.X86.Scrub
public import VerifiedGarbage.Impl.AesGcm.X86.Fn
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

/-! # AES-GCM (NIST SP 800-38D) on x86 -/

@[expose] public section

namespace VG.Artifacts.AesGcm.X86.AesCtr32

open VG.Proof.AesGcm.X86 VG.Proof.AesGcm.X86.Scrub

/-- The artifacts calling the implementation `c` of `vg_aes_ctr32_to`, and no GHASH. -/
def artifacts (c : Proof.Aes.X86.Ctr32Impl) : List Artifact :=
  let v : GcmImpl := { ctr := c, gh := GhashName.scalar.impl }
  [
  Spec.Gcm.initApi.artifact X86.target {
    suffix := c.suffix
    code := Impl.AesGcm.X86.Fn.init v.callees
    verified := .scrubbed (init_scrubbed v)
    spSafe := init_spSafeF v }]

end VG.Artifacts.AesGcm.X86.AesCtr32

-- AES-GCM (NIST SP 800-38D) on x86
namespace VG.Artifacts.AesGcm.X86.AesGcm

open VG.Proof.AesGcm.X86 VG.Proof.AesGcm.X86.Scrub

/-- The artifacts calling the implementations `v`. -/
def artifactsOf (v : GcmImpl) : List Artifact := [
  Spec.Gcm.streamEncryptApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.AesGcm.X86.Fn.streamEncrypt v.callees
    verified := .scrubbed (streamEncrypt_scrubbed v)
    spSafe := streamEncrypt_spSafeF v },
  Spec.Gcm.streamDecryptApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.AesGcm.X86.Fn.streamDecrypt v.callees
    verified := .scrubbed (streamDecrypt_scrubbed v)
    spSafe := streamDecrypt_spSafeF v },
  Spec.Gcm.streamFinishApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.AesGcm.X86.Fn.streamFinish v.callees
    verified := .scrubbed (streamFinish_scrubbed v)
    spSafe := streamFinish_spSafeF v },
  Spec.Gcm.streamVerifyApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.AesGcm.X86.Fn.streamVerify v.callees
    verified := .scrubbed (streamVerify_scrubbed v)
    spSafe := streamVerify_spSafeF v },
  Spec.Gcm.sealApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.AesGcm.X86.Fn.«seal» v.callees
    verified := .scrubbed (seal_scrubbed v)
    spSafe := seal_spSafeF v },
  Spec.Gcm.openApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.AesGcm.X86.Fn.«open» v.callees
    verified := .scrubbed (open_scrubbed v)
    spSafe := open_spSafeF v }]

/-- `vg_aes_gcm_seal_gather`, calling the instance of `vg_aes_gcm_seal` of the
implementations `v`, without its cleanup (`vg_aes_gcm_seal<suffix>_core`). -/
def artifactsGather (v : GcmImpl) : List Artifact := [
  Spec.Gcm.sealGatherApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.AesGcm.X86.Fn.sealGather v.callees v.suffix
    verified := .scrubbed (sealGather_scrubbed v)
    spSafe := sealGather_spSafeF v }]

/-- `vg_aes_gcm_open_to`, calling `vg_aes_ctr32_to` of the implementations `v`. -/
def artifactsOpenTo (v : GcmImpl) : List Artifact := [
  Spec.Gcm.openToApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.AesGcm.X86.Fn.openTo v.callees (OpenTo.toFn v)
    verified := .scrubbed (openTo_scrubbed v)
    spSafe := openTo_spSafeF v }]

/-- The artifacts of a variant, from the implementations it names. -/
def artifacts (v : GcmVariant) : List Artifact :=
  artifactsOf v.impl ++ artifactsGather v.impl ++ artifactsOpenTo v.impl

end VG.Artifacts.AesGcm.X86.AesGcm

-- AES-GCM's GHASH-only functions on x86
namespace VG.Artifacts.AesGcm.X86.Ghash

open VG.Proof.AesGcm.X86 VG.Proof.AesGcm.X86.Scrub

/-- The artifacts calling the implementation `n` of `vg_ghash`, and no AES. -/
def artifacts (n : GhashName) : List Artifact :=
  let v : GcmImpl := { ctr := Proof.Aes.X86.Ctr32Impl.scalar, gh := n.impl }
  [
  Spec.Gcm.streamAadApi.artifact X86.target {
    suffix := n.impl.suffix
    code := Impl.AesGcm.X86.Fn.streamAad v.callees
    verified := .scrubbed (streamAad_scrubbed v)
    spSafe := streamAad_spSafeF v },
  Spec.Gcm.streamInitApi.artifact X86.target {
    suffix := n.impl.suffix
    code := Impl.AesGcm.X86.Fn.streamInit v.callees
    verified := .scrubbed (streamInit_scrubbed v)
    spSafe := streamInit_spSafeF v }]

end VG.Artifacts.AesGcm.X86.Ghash

namespace VG.Artifacts.AesGcm.X86

def artifacts : List Artifact :=
  (VG.Proof.Variants.AesCtr32.X86.variants.flatMap fun v => AesCtr32.artifacts v) ++
  (VG.Proof.Variants.AesGcm.X86.variants.flatMap fun v => AesGcm.artifacts v) ++
  (VG.Proof.Variants.Ghash.X86.variants.flatMap fun v => Ghash.artifacts v)

end VG.Artifacts.AesGcm.X86
