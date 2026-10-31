module

public import VerifiedGarbage.Proof.AesGcm.X86.GhashImpls
public import VerifiedGarbage.Proof.AesGcm.X86.Gather.Verified
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
import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyRecurrence
import VerifiedGarbage.Proof.Aes.X86.AesNi.Load
import VerifiedGarbage.Proof.Aes.X86.AesNi.Prologue
import VerifiedGarbage.Proof.Aes.X86.AesNi.Restore
import VerifiedGarbage.Proof.Aes.X86.AesNi.Tail
import VerifiedGarbage.Proof.AesGcm.X86.CryptHead
import VerifiedGarbage.Proof.AesGcm.X86.CryptTail
import VerifiedGarbage.Proof.AesGcm.X86.CryptWhole
import VerifiedGarbage.Proof.AesGcm.X86.Flush
import VerifiedGarbage.Proof.AesGcm.X86.Gather.CT
import VerifiedGarbage.Proof.AesGcm.X86.Gather.Fn
import VerifiedGarbage.Proof.AesGcm.X86.Init
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.X86.StackScratch
import VerifiedGarbage.Proof.Gcm.SealGather

/-! # AES-GCM (NIST SP 800-38D) on x86 -/

@[expose] public section

namespace VG.Generic.AesGcm.X86.AesGcm

open VG.Proof.AesGcm.X86

/-- The artifacts calling the implementations `v`. -/
def artifactsOf (v : GcmImpl) : List Artifact := [
  Spec.Gcm.initApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86.withStackScratch 2580 3 (Impl.AesGcm.X86.init v.callees)
    stack := 2608
    verified := init_framed v
    spSafe := withStackScratch_spSafe (init_spSafe v)
    features := (v.ctr.features) },
  Spec.Gcm.streamAadApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86.withStackScratch 2592 6 (Impl.AesGcm.X86.streamAad v.callees)
    stack := 2616
    verified := streamAad_framed v
    spSafe := withStackScratch_spSafe (streamAad_spSafe v)
    features := v.gh.features },
  Spec.Gcm.streamInitApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86.withStackScratch 2584 4 (Impl.AesGcm.X86.streamInit v.callees)
    stack := 2608
    verified := streamInit_framed v
    spSafe := withStackScratch_spSafe (streamInit_spSafe v)
    features := v.gh.features },
  Spec.Gcm.streamEncryptApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86.withStackScratch 2604 9 (Impl.AesGcm.X86.streamEncrypt v.callees)
    stack := 2632
    verified := streamEncrypt_framed v
    spSafe := withStackScratch_spSafe (streamEncrypt_spSafe v)
    features := v.features },
  Spec.Gcm.streamDecryptApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86.withStackScratch 2604 9 (Impl.AesGcm.X86.streamDecrypt v.callees)
    stack := 2632
    verified := streamDecrypt_framed v
    spSafe := withStackScratch_spSafe (streamDecrypt_spSafe v)
    features := v.features },
  Spec.Gcm.streamFinishApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86.withStackScratch 2600 8 (Impl.AesGcm.X86.streamFinish v.callees)
    stack := 2628
    verified := streamFinish_framed v
    spSafe := withStackScratch_spSafe (streamFinish_spSafe v)
    features := v.features },
  Spec.Gcm.streamVerifyApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86.withStackScratch 2604 9 (Impl.AesGcm.X86.streamVerify v.callees)
    stack := 2632
    verified := streamVerify_framed v
    spSafe := withStackScratch_spSafe (streamVerify_spSafe v)
    features := v.features },
  Spec.Gcm.sealApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86.withStackScratch 2604 9 (Impl.AesGcm.X86.«seal» v.callees)
    stack := 2632
    verified := seal_framed v
    spSafe := withStackScratch_spSafe (seal_spSafe v)
    features := v.features },
  Spec.Gcm.openApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86.withStackScratch 2608 10 (Impl.AesGcm.X86.«open» v.callees)
    stack := 2636
    verified := open_framed v
    spSafe := withStackScratch_spSafe (open_spSafe v)
    features := v.features }]

/-- `vg_aes_gcm_seal_gather`, calling the instance of `vg_aes_gcm_seal` of the implementations `v`. -/
def artifactsGather (v : GcmImpl) : List Artifact := [
  Spec.Gcm.sealGatherApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.AesGcm.X86.SealGather.sealGather (Gather.sealFn v).name (Gather.sealFn v).code
    stack := 2684
    verified := Gather.sealGather_verified (Gather.sealFn v)
    spSafe := Gather.sealGather_spSafe v
    features := v.features }]

/-- The artifacts of a variant, from the implementations it names. -/
def artifacts (v : GcmVariant) : List Artifact := artifactsOf v.impl ++ artifactsGather v.impl

end VG.Generic.AesGcm.X86.AesGcm
