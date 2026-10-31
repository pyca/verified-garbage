module

public import VerifiedGarbage.Proof.Sm4Gcm.X86_64.Frame
public import VerifiedGarbage.Proof.AesGcm.X86_64.Frame
public import VerifiedGarbage.Proof.AesGcm.X86_64.GhashImpls
public import VerifiedGarbage.Proof.Aes.X86_64.Variant
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch

/-! # SM4-GCM (NIST SP 800-38D, RFC 8998) on x86-64 -/

@[expose] public section

namespace VG.Generic.Ghash.X86_64.Sm4Gcm

open VG.Proof.AesGcm.X86_64 (GcmImpl GhashName KeyImpl)
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.Sm4Gcm.X86_64

/-- The artifacts calling the implementation `n` of `vg_ghash`. -/
def artifacts (n : GhashName) : List Artifact :=
  let v : GcmImpl := { ctr := Ctr32Impl.scalar, key := KeyImpl.scalar, gh := n.impl }
  [Spec.Sm4.Gcm.sealApi.artifact X86_64.target {
    suffix := n.impl.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 2592 2 (Impl.Sm4Gcm.X86_64.«seal» v.callees)
    stack := 5816
    verified := seal_framed v
    spSafe := X86_64.withStackArgScratch_spSafe (seal_spSafe v)
    features := n.impl.features },
  Spec.Sm4.Gcm.openApi.artifact X86_64.target {
    suffix := n.impl.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 2600 3 (Impl.Sm4Gcm.X86_64.«open» v.callees)
    stack := 5824
    verified := open_framed v
    spSafe := X86_64.withStackArgScratch_spSafe (open_spSafe v)
    features := n.impl.features },
  Spec.Sm4.Gcm.streamInitApi.artifact X86_64.target {
    suffix := n.impl.suffix
    code := Impl.StackScratch.X86_64.withStackScratch 2568 .r8
      (Impl.AesGcm.X86_64.streamInit v.callees)
    stack := 2576
    verified := Proof.AesGcm.X86_64.streamInit_framed v
    spSafe := X86_64.withStackScratch_spSafe_of (Proof.AesGcm.X86_64.streamInit_spSafe v)
    features := n.impl.features },
  Spec.Sm4.Gcm.streamAadApi.artifact X86_64.target {
    suffix := n.impl.suffix
    code := Impl.StackScratch.X86_64.withStackScratch 2568 .r9
      (Impl.AesGcm.X86_64.streamAad v.callees)
    stack := 2576
    verified := Proof.AesGcm.X86_64.streamAad_framed v
    spSafe := X86_64.withStackScratch_spSafe_of (Proof.AesGcm.X86_64.streamAad_spSafe v)
    features := n.impl.features },
  Spec.Sm4.Gcm.streamEncryptApi.artifact X86_64.target {
    suffix := n.impl.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 2576 0
      (Impl.Sm4Gcm.X86_64.streamEncrypt v.callees)
    stack := 5800
    verified := streamEncrypt_framed v
    spSafe := X86_64.withStackArgScratch_spSafe (streamEncrypt_spSafe v)
    features := n.impl.features },
  Spec.Sm4.Gcm.streamDecryptApi.artifact X86_64.target {
    suffix := n.impl.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 2576 0
      (Impl.Sm4Gcm.X86_64.streamDecrypt v.callees)
    stack := 5800
    verified := streamDecrypt_framed v
    spSafe := X86_64.withStackArgScratch_spSafe (streamDecrypt_spSafe v)
    features := n.impl.features },
  Spec.Sm4.Gcm.streamFinishApi.artifact X86_64.target {
    suffix := n.impl.suffix
    code := Impl.StackScratch.X86_64.withStackScratch 2568 .r9
      (Impl.Sm4Gcm.X86_64.streamFinish v.callees)
    stack := 5792
    verified := streamFinish_framed v
    spSafe := X86_64.withStackScratch_spSafe_of (streamFinish_spSafe v)
    features := n.impl.features },
  Spec.Sm4.Gcm.streamVerifyApi.artifact X86_64.target {
    suffix := n.impl.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 2576 0
      (Impl.Sm4Gcm.X86_64.streamVerify v.callees)
    stack := 5800
    verified := streamVerify_framed v
    spSafe := X86_64.withStackArgScratch_spSafe (streamVerify_spSafe v)
    features := n.impl.features }]

end VG.Generic.Ghash.X86_64.Sm4Gcm
