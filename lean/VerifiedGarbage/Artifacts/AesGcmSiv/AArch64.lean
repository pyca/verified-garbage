module

public import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Verified
public import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Stitch.Verified
public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.Instances
public import VerifiedGarbage.Proof.Gcm.AArch64.Pmull.Ghash
public import VerifiedGarbage.Proof.AesGcm.AArch64.Verified
public import VerifiedGarbage.Proof.AesGcm.AArch64.GhashImpls
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.AesGcm.AArch64.Cmp
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fn
public import VerifiedGarbage.Proof.AesGcm.AArch64.Init
public import VerifiedGarbage.Proof.AesGcm.AArch64.Rel
public import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Crypt
public import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Derive
public import VerifiedGarbage.Proof.AesGcmSiv.AArch64.FnCT
public import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Keys
public import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Polyval
public import VerifiedGarbage.Proof.Cmac.Dbl32
public import VerifiedGarbage.Proof.Cmac.Frame
public import VerifiedGarbage.Proof.Cmac.Spec
public import VerifiedGarbage.Proof.Cmac.Stream
public import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.Framework.AArch64.RelCT
public import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Range
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Gcm.Be64
public import VerifiedGarbage.Proof.Gcm.Bits
public import VerifiedGarbage.Proof.Gcm.Powers
public import VerifiedGarbage.Proof.Siv.Spec
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.Variants.AesGcm.AArch64

/-! # AES-GCM-SIV (RFC 8452) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.AesGcmSiv.AArch64

open VG.Proof.AesGcm.AArch64 (GcmImpl GcmVariant)
open VG.Proof.AesGcmSiv.AArch64

/-- The artifacts calling the implementations `v`. -/
def artifactsOf (v : GcmImpl) : List Artifact := [
  Spec.GcmSiv.sealApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.StackScratch.AArch64.withStackArgScratch 3824 0 (Stitch.sealCode v)
    stack := 3824
    verified := Proof.AesGcmSiv.seal_keyed (Stitch.sealCode_framed Proof.Gcm.AArch64.Pmull.prepPow Proof.Gcm.AArch64.Stitch.gh8Ok v)
    features := v.stitchFeatures },
  Spec.GcmSiv.openApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.StackScratch.AArch64.withStackArgScratch 3824 0 (Stitch.openCode v)
    stack := 3824
    verified := Proof.AesGcmSiv.open_keyed (Stitch.openCode_framed Proof.Gcm.AArch64.Pmull.prepPow Proof.Gcm.AArch64.Stitch.gh8Ok v)
    features := v.stitchFeatures }]

/-- The artifacts of a variant, from the implementations it names. -/
def artifactsFor (v : GcmVariant) : List Artifact := artifactsOf v.impl

def artifacts : List Artifact :=
  VG.Proof.Variants.AesGcm.AArch64.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.AesGcmSiv.AArch64
