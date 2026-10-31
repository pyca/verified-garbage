module

public import VerifiedGarbage.Proof.AesGcmSiv.X86.Frame
public import VerifiedGarbage.Proof.GcmSiv.Polyval
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.AesGcm.X86.GhashImpls
public import VerifiedGarbage.Proof.AesGcm.X86.Verified
import VerifiedGarbage.Proof.AesGcm.X86.Frame
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
import VerifiedGarbage.Generic.AesGcm.X86.AesGcm
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
import VerifiedGarbage.Proof.AesGcmSiv.X86.Cmp
import VerifiedGarbage.Proof.AesGcmSiv.X86.Derive
import VerifiedGarbage.Proof.AesGcmSiv.X86.FnCT
import VerifiedGarbage.Proof.AesGcmSiv.X86.Open
import VerifiedGarbage.Proof.AesGcmSiv.X86.Polyval
import VerifiedGarbage.Proof.AesGcmSiv.X86.Run
import VerifiedGarbage.Proof.AesGcmSiv.X86.TagIO
import VerifiedGarbage.Proof.Cmac.Block
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.X86.StackScratch
import VerifiedGarbage.Proof.Gcm.Be64
import VerifiedGarbage.Proof.Gcm.Bits
import VerifiedGarbage.Proof.Gcm.SealGather
import VerifiedGarbage.Proof.GcmSiv.Words32
import VerifiedGarbage.Proof.Siv.Spec

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
    stack := 2884
    verified := seal_framed v VG.Proof.GcmSiv.Polyval.tagInput_eq_tagInputG
    spSafe := Proof.AesGcm.X86.withStackScratch_spSafe (seal_spSafe v)
    features := v.features },
  Spec.GcmSiv.openApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86.withStackScratch 2856 8 (Impl.AesGcmSiv.X86.«open» v.callees)
    stack := 2884
    verified := open_framed v VG.Proof.GcmSiv.Polyval.tagInput_eq_tagInputG
    spSafe := Proof.AesGcm.X86.withStackScratch_spSafe (open_spSafe v)
    features := v.features }]

/-- The artifacts of a variant, from the implementations it names. -/
def artifacts (v : GcmVariant) : List Artifact := artifactsOf v.impl

end VG.Generic.AesGcm.X86.AesGcmSiv
