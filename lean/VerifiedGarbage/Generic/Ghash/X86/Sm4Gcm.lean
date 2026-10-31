module

public import VerifiedGarbage.Proof.AesGcm.X86.GhashImpls
public import VerifiedGarbage.Proof.Aes.X86.VariantProof
public import VerifiedGarbage.Proof.Sm4Gcm.X86.Frame
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SM4-GCM (NIST SP 800-38D, RFC 8998) on x86 -/

@[expose] public section

namespace VG.Generic.Ghash.X86.Sm4Gcm

open VG.Proof.Sm4Gcm.X86
open VG.Proof.AesGcm.X86 (GcmImpl withStackScratch_spSafe)

/-- The artifacts calling the implementations `v`. -/
def artifactsOf (v : GcmImpl) : List Artifact := [
  Spec.Sm4.Gcm.streamInitApi.artifact X86.target {
    suffix := v.gh.suffix
    code := Impl.StackScratch.X86.withStackScratch 2584 4 (Impl.AesGcm.X86.streamInit v.callees)
    stack := 2608
    verified := Proof.AesGcm.X86.streamInit_framed v
    spSafe := withStackScratch_spSafe (Proof.AesGcm.X86.streamInit_spSafe v)
    features := v.gh.features },
  Spec.Sm4.Gcm.streamAadApi.artifact X86.target {
    suffix := v.gh.suffix
    code := Impl.StackScratch.X86.withStackScratch 2592 6 (Impl.AesGcm.X86.streamAad v.callees)
    stack := 2616
    verified := Proof.AesGcm.X86.streamAad_framed v
    spSafe := withStackScratch_spSafe (Proof.AesGcm.X86.streamAad_spSafe v)
    features := v.gh.features },
  Spec.Sm4.Gcm.streamEncryptApi.artifact X86.target {
    suffix := v.gh.suffix
    code := Impl.StackScratch.X86.withStackScratch 2600 8 (Impl.Sm4Gcm.X86.streamEncrypt v.callees)
    stack := 4136
    verified := streamEncrypt_framed v
    spSafe := withStackScratch_spSafe (streamEncrypt_spSafe v)
    features := v.gh.features },
  Spec.Sm4.Gcm.streamDecryptApi.artifact X86.target {
    suffix := v.gh.suffix
    code := Impl.StackScratch.X86.withStackScratch 2600 8 (Impl.Sm4Gcm.X86.streamDecrypt v.callees)
    stack := 4136
    verified := streamDecrypt_framed v
    spSafe := withStackScratch_spSafe (streamDecrypt_spSafe v)
    features := v.gh.features },
  Spec.Sm4.Gcm.streamFinishApi.artifact X86.target {
    suffix := v.gh.suffix
    code := Impl.StackScratch.X86.withStackScratch 2596 7 (Impl.Sm4Gcm.X86.streamFinish v.callees)
    stack := 4132
    verified := streamFinish_framed v
    spSafe := withStackScratch_spSafe (streamFinish_spSafe v)
    features := v.gh.features },
  Spec.Sm4.Gcm.streamVerifyApi.artifact X86.target {
    suffix := v.gh.suffix
    code := Impl.StackScratch.X86.withStackScratch 2600 8 (Impl.Sm4Gcm.X86.streamVerify v.callees)
    stack := 4136
    verified := streamVerify_framed v
    spSafe := withStackScratch_spSafe (streamVerify_spSafe v)
    features := v.gh.features },
  Spec.Sm4.Gcm.sealApi.artifact X86.target {
    suffix := v.gh.suffix
    code := Impl.StackScratch.X86.withStackScratch 2600 8 (Impl.Sm4Gcm.X86.«seal» v.callees)
    stack := 4136
    verified := seal_framed v
    spSafe := withStackScratch_spSafe (seal_spSafe v)
    features := v.gh.features },
  Spec.Sm4.Gcm.openApi.artifact X86.target {
    suffix := v.gh.suffix
    code := Impl.StackScratch.X86.withStackScratch 2604 9 (Impl.Sm4Gcm.X86.«open» v.callees)
    stack := 4140
    verified := open_framed v
    spSafe := withStackScratch_spSafe (open_spSafe v)
    features := v.gh.features }]

/-- The artifacts of a variant, from the implementation of `vg_ghash` it names. -/
def artifacts (v : Proof.AesGcm.X86.GhashName) : List Artifact :=
  artifactsOf ⟨Proof.Aes.X86.Ctr32Impl.scalar, v.impl⟩

end VG.Generic.Ghash.X86.Sm4Gcm
