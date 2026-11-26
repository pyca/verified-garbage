module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.GcmSiv.Contract
import VerifiedGarbage.Impl.AesGcmSiv.AArch64.Fn
import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Stitch.Verified
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Variants.AesGcm.AArch64
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # AES-GCM-SIV (RFC 8452) on AArch64 -/

namespace VG.Artifacts.AesGcmSiv.AArch64

open VG.Proof.AesGcm.AArch64 (GcmVariant)
open VG.Proof.AesGcmSiv.AArch64

/-- The artifacts of a variant, from the implementations it names. -/
def artifactsFor (g : GcmVariant) : List (Artifact AArch64.target) := [
  Spec.GcmSiv.sealApi.artifact AArch64.target {
    suffix := g.impl.suffix
    code := Impl.AesGcmSiv.AArch64.Fn.seal g.calls
    verified := Proof.AesGcmSiv.AArch64.Stitch.seal_scrubbed g },
  Spec.GcmSiv.openApi.artifact AArch64.target {
    suffix := g.impl.suffix
    code := Impl.AesGcmSiv.AArch64.Fn.open g.calls
    verified := Proof.AesGcmSiv.AArch64.Stitch.open_scrubbed g }]

public def artifacts : List (Artifact AArch64.target) :=
  VG.Proof.Variants.AesGcm.AArch64.variants.flatMap artifactsFor

spec_apis artifacts

end VG.Artifacts.AesGcmSiv.AArch64
