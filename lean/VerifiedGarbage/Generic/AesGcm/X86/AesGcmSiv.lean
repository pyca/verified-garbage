module

public import VerifiedGarbage.Proof.AesGcmSiv.X86.Frame
public import VerifiedGarbage.Proof.GcmSiv.Polyval
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.AesGcm.X86.GhashImpls
public import VerifiedGarbage.Proof.AesGcm.X86.Verified
public import VerifiedGarbage.Proof.AesGcm.X86.Frame
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Generic.AesGcm.X86.AesGcm
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
public import VerifiedGarbage.Proof.AesGcmSiv.X86.Cmp
public import VerifiedGarbage.Proof.AesGcmSiv.X86.Derive
public import VerifiedGarbage.Proof.AesGcmSiv.X86.FnCT
public import VerifiedGarbage.Proof.AesGcmSiv.X86.Open
public import VerifiedGarbage.Proof.AesGcmSiv.X86.Polyval
public import VerifiedGarbage.Proof.AesGcmSiv.X86.Run
public import VerifiedGarbage.Proof.AesGcmSiv.X86.TagIO
public import VerifiedGarbage.Proof.Cmac.Block
public import VerifiedGarbage.Proof.Cmac.Frame
public import VerifiedGarbage.Proof.Cmac.Spec
public import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Framework.X86.SseTaint
public import VerifiedGarbage.Proof.Framework.X86.StackScratch
public import VerifiedGarbage.Proof.Gcm.Be64
public import VerifiedGarbage.Proof.Gcm.Bits
public import VerifiedGarbage.Proof.Gcm.SealGather
public import VerifiedGarbage.Proof.GcmSiv.Words32
public import VerifiedGarbage.Proof.Siv.Spec
public import VerifiedGarbage.TCB.X86.Print

/-! # AES-GCM-SIV (RFC 8452) on x86 -/

@[expose] public section

namespace VG.Generic.AesGcm.X86.AesGcmSiv

open VG.Proof.AesGcm.X86 (GcmImpl GcmVariant)
open VG.Proof.AesGcmSiv.X86

/-- The artifacts calling the implementations `v`. -/
def artifactsOf (v : GcmImpl) : List Artifact := [
  Spec.GcmSiv.sealApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86.withStackScratch 2856 8 (Impl.AesGcmSiv.X86.«seal» v.callees)
    stack := 2888
    verified := Proof.AesGcmSiv.seal_keyed (seal_framed v VG.Proof.GcmSiv.Polyval.tagInput_eq_tagInputG)
    spSafe := Proof.AesGcm.X86.withStackScratch_spSafe (seal_spSafe v)
    features := v.features },
  Spec.GcmSiv.openApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86.withStackScratch 2856 8 (Impl.AesGcmSiv.X86.«open» v.callees)
    stack := 2888
    verified := Proof.AesGcmSiv.open_keyed (open_framed v VG.Proof.GcmSiv.Polyval.tagInput_eq_tagInputG)
    spSafe := Proof.AesGcm.X86.withStackScratch_spSafe (open_spSafe v)
    features := v.features }]

/-- The artifacts of a variant, from the implementations it names. -/
def artifacts (v : GcmVariant) : List Artifact := artifactsOf v.impl

end VG.Generic.AesGcm.X86.AesGcmSiv
