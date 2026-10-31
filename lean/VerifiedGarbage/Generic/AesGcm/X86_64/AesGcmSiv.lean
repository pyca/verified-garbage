module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Instances
public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Instances
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
public import VerifiedGarbage.Proof.Aes.X86_64.Decrypt
public import VerifiedGarbage.Proof.Aes.X86_64.VaesBlocks.Dec
public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Fn
public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Keys
public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.Ctr
public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.Gh
public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.SealCT
public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.Setup
public import VerifiedGarbage.Proof.Ocb.Spec
import VerifiedGarbage.Proof.Aes.X86_64.Decrypt
import VerifiedGarbage.Proof.Aes.X86_64.VaesBlocks.Dec
import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Fn
import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Keys
import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.Ctr
import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.Gh
import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.SealCT
import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.Setup
import VerifiedGarbage.Proof.Ocb.Spec

/-! # AES-GCM-SIV (RFC 8452) on x86-64 -/

@[expose] public section

namespace VG.Generic.AesGcm.X86_64.AesGcmSiv

open VG.Proof.AesGcm.X86_64 (GcmImpl GcmVariant)
open VG.Proof.AesGcmSiv.X86_64

/-- The artifacts calling the implementations `v`. -/
def artifactsOf (v : GcmImpl) : List Artifact := [
  Spec.GcmSiv.sealApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 3848 2 (sealCode v)
    stack := 3856
    verified := sealCode_framed v
    spSafe := X86_64.withStackArgScratch_spSafe (sealCode_spSafe v)
    features := features v },
  Spec.GcmSiv.openApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 3848 2 (openCode v)
    stack := 3856
    verified := openCode_framed v
    spSafe := X86_64.withStackArgScratch_spSafe (openCode_spSafe v)
    features := features v }]

/-- The artifacts of a variant, from the implementations it names. -/
def artifacts (v : GcmVariant) : List Artifact := artifactsOf v.impl

end VG.Generic.AesGcm.X86_64.AesGcmSiv
