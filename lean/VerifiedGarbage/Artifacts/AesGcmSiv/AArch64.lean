module

public import VerifiedGarbage.Impl.AesGcmSiv.AArch64.Fn
public import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Stitch.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.Variants.AesGcm.AArch64

/-! # AES-GCM-SIV (RFC 8452) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.AesGcmSiv.AArch64

open VG.Proof.AesGcm.AArch64 (GcmVariant)
open VG.Proof.AesGcmSiv.AArch64

/-- The artifacts of a variant, from the implementations it names. -/
def artifactsFor (g : GcmVariant) : List Artifact := [
  Spec.GcmSiv.sealApi.artifact AArch64.target {
    suffix := g.impl.suffix
    code := Impl.AesGcmSiv.AArch64.Fn.seal g.calls
    verified := .scrubbed (Stitch.seal_scrubbed g) },
  Spec.GcmSiv.openApi.artifact AArch64.target {
    suffix := g.impl.suffix
    code := Impl.AesGcmSiv.AArch64.Fn.open g.calls
    verified := .scrubbed (Stitch.open_scrubbed g) }]

def artifacts : List Artifact :=
  VG.Proof.Variants.AesGcm.AArch64.variants.flatMap artifactsFor

end VG.Artifacts.AesGcmSiv.AArch64
