module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.GcmSiv.Contract
import VerifiedGarbage.Impl.AesGcmSiv.X86
import VerifiedGarbage.Proof.AesGcmSiv.X86.Frame
import VerifiedGarbage.Proof.GcmSiv.Polyval
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.AesGcm.X86.GhashImpls
import VerifiedGarbage.Proof.AesGcm.X86.Verified
import VerifiedGarbage.Proof.AesGcm.X86.Frame
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
import VerifiedGarbage.Proof.Variants.AesGcm.X86
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # AES-GCM-SIV (RFC 8452) on x86 -/

namespace VG.Artifacts.AesGcmSiv.X86

open VG.Proof.AesGcm.X86 (GcmImpl GcmVariant)
open VG.Proof.AesGcmSiv.X86

/-- The artifacts calling the implementations `v`. -/
def artifactsOf (v : GcmImpl) : List (Artifact X86.target) := [
  Spec.GcmSiv.sealApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.AesGcmSiv.X86.Fn.«seal» v.callees
    verified := Proof.AesGcmSiv.X86.Scrub.seal_scrubbed v VG.Proof.GcmSiv.Polyval.tagInput_eq_tagInputG
    spSafe := Proof.AesGcmSiv.X86.Scrub.seal_fnSpSafe v },
  Spec.GcmSiv.openApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.AesGcmSiv.X86.Fn.«open» v.callees
    verified := Proof.AesGcmSiv.X86.Scrub.open_scrubbed v VG.Proof.GcmSiv.Polyval.tagInput_eq_tagInputG
    spSafe := Proof.AesGcmSiv.X86.Scrub.open_fnSpSafe v }]

/-- The artifacts of a variant, from the implementations it names. -/
def artifactsFor (v : GcmVariant) : List (Artifact X86.target) := artifactsOf v.impl

public def artifacts : List (Artifact X86.target) :=
  VG.Proof.Variants.AesGcm.X86.variants.flatMap fun v => artifactsFor v

spec_apis artifacts

end VG.Artifacts.AesGcmSiv.X86
