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
public import VerifiedGarbage.TCB.X86_64.Print
public import VerifiedGarbage.Proof.Variants.AesGcm.X86_64

/-! # AES-GCM-SIV (RFC 8452) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.AesGcmSiv.X86_64

open VG.Proof.AesGcm.X86_64 (GcmImpl GcmVariant)
open VG.Proof.AesGcmSiv.X86_64

/-- The artifacts calling the implementations `v`. -/
def artifactsOf (v : GcmImpl) : List Artifact := [
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
def wideArtifactsOf (v : GcmImpl) : List Artifact := [
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
def artifactsFor (v : GcmImpl) : List Artifact :=
  (if hasWide v then wideArtifactsOf v else []) ++ if hasNarrow v then artifactsOf v else []

def artifacts : List Artifact :=
  (sivImpls (VG.Proof.Variants.AesGcm.X86_64.variants.map (·.impl))).flatMap artifactsFor

end VG.Artifacts.AesGcmSiv.X86_64
