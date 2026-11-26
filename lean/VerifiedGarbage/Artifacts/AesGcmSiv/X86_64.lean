module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.GcmSiv.Contract
import VerifiedGarbage.Proof.AesGcm.X86_64.Instances
import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Instances
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
import VerifiedGarbage.Proof.Aes.X86_64.Blocks
import VerifiedGarbage.Proof.Aes.X86_64.VaesBlocks.Dec
import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Fn
import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Keys
import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.Ctr
import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.Gh
import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.SealCT
import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.Setup
import VerifiedGarbage.Proof.Ocb.Spec
import VerifiedGarbage.Proof.Variants.AesGcm.X86_64
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # AES-GCM-SIV (RFC 8452) on x86-64 -/

namespace VG.Artifacts.AesGcmSiv.X86_64

open VG.Proof.AesGcm.X86_64 (GcmImpl GcmVariant)
open VG.Proof.AesGcmSiv.X86_64

/-- The artifacts calling the implementations `v`. -/
def artifactsOf (v : GcmImpl) : List (Artifact X86_64.target) := [
  Spec.GcmSiv.sealApi.artifact X86_64.target
    (if sivReg v then
      { suffix := v.suffix
        code := Impl.AesGcmSiv.X86_64.Fn.sealReg (regLevel (loopsOf v)) (loopsOf v)
        verified := Proof.AesGcmSiv.X86_64.sealReg_scrubbed v
        spSafe := Proof.AesGcmSiv.X86_64.sealReg_spSafeFn v }
    else
      { suffix := v.suffix
        code := Impl.AesGcmSiv.X86_64.Fn.sealSoft (softLevel v (sivWide v) (loopsOf v)) v.callees (ecbFn v)
            (sivWide v) (loopsOf v)
        verified := Proof.AesGcmSiv.X86_64.sealSoft_scrubbed v (sivWide v)
        spSafe := Proof.AesGcmSiv.X86_64.sealSoft_spSafeFn v (sivWide v) }),
  Spec.GcmSiv.openApi.artifact X86_64.target
    (if sivReg v then
      { suffix := v.suffix
        code := Impl.AesGcmSiv.X86_64.Fn.openReg (regLevel (loopsOf v)) (loopsOf v)
        verified := Proof.AesGcmSiv.X86_64.openReg_scrubbed v
        spSafe := Proof.AesGcmSiv.X86_64.openReg_spSafeFn v }
    else
      { suffix := v.suffix
        code := Impl.AesGcmSiv.X86_64.Fn.openSoft (softLevel v (sivWide v) (loopsOf v)) v.callees (ecbFn v)
            (sivWide v) (loopsOf v)
        verified := Proof.AesGcmSiv.X86_64.openSoft_scrubbed v (sivWide v)
        spSafe := Proof.AesGcmSiv.X86_64.openSoft_spSafeFn v (sivWide v) })]

/-- The instances with the AVX2 copies (`_avx2`), for a variant that has
them (`hasWide`), by the lengths where the variant's code does not take
them already. -/
def wideArtifactsOf (v : GcmImpl) : List (Artifact X86_64.target) := [
  Spec.GcmSiv.sealApi.artifact X86_64.target {
    suffix := v.suffix ++ "_avx2"
    code := Impl.AesGcmSiv.X86_64.Fn.sealAvx2 (softLevel v true (loopsOf v)) v.callees (ecbFn v) (sivWide v) (loopsOf v)
    verified := Proof.AesGcmSiv.X86_64.sealAvx2_scrubbed v
    spSafe := Proof.AesGcmSiv.X86_64.sealAvx2_spSafeFn v },
  Spec.GcmSiv.openApi.artifact X86_64.target {
    suffix := v.suffix ++ "_avx2"
    code := Impl.AesGcmSiv.X86_64.Fn.openAvx2 (softLevel v true (loopsOf v)) v.callees (ecbFn v) (sivWide v) (loopsOf v)
    verified := Proof.AesGcmSiv.X86_64.openAvx2_scrubbed v
    spSafe := Proof.AesGcmSiv.X86_64.openAvx2_spSafeFn v }]

/-- The artifacts of the implementations `v`: those with the AVX2 copies,
where they may run (`hasWide`), first, which its dispatchers then try first;
then those without them, where they may run where the others cannot
(`hasNarrow`). -/
def artifactsFor (v : GcmImpl) : List (Artifact X86_64.target) :=
  (if hasWide v then wideArtifactsOf v else []) ++ if hasNarrow v then artifactsOf v else []

public def artifacts : List (Artifact X86_64.target) :=
  (sivImpls (VG.Proof.Variants.AesGcm.X86_64.variants.map (·.impl))).flatMap artifactsFor

spec_apis artifacts

end VG.Artifacts.AesGcmSiv.X86_64
