module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Instances
public import VerifiedGarbage.Proof.Aes.X86_64.Variant
public import VerifiedGarbage.Proof.AesGcm.X86_64.GhashImpls
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
public import VerifiedGarbage.TCB.X86_64.Print

/-! # AES-GCM's functions on x86-64 that call AES and GHASH but no stitched loop -/

@[expose] public section

namespace VG.Generic.AesCtr32.Ghash.X86_64.AesGcm

open VG.Proof.AesGcm.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)

/-- The artifacts calling the implementation `c` of `vg_aes_ctr32` and `n` of
`vg_ghash`. -/
def artifacts (c : Ctr32Impl) (n : GhashName) : List Artifact :=
  let v : GcmImpl :=
    { ctr := c, key := if c.features.isEmpty then KeyImpl.scalar else KeyImpl.aesni,
      gh := n.impl }
  [
  Spec.Gcm.streamFinishApi.artifact X86_64.target {
    select := true
    suffix := c.suffix ++ n.impl.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 2576 0 (Impl.AesGcm.X86_64.streamFinish v.callees)
    stack := 2584
    verified := Proof.AesGcm.streamFinish_keyed (streamFinish_framed v)
    spSafe := X86_64.withStackArgScratch_spSafe (streamFinish_spSafe v)
    features := (v.ctr.features ++ v.gh.features).dedup },
  Spec.Gcm.streamVerifyApi.artifact X86_64.target {
    select := true
    suffix := c.suffix ++ n.impl.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamVerify v.callees)
    stack := 2592
    verified := Proof.AesGcm.streamVerify_keyed (streamVerify_framed v)
    spSafe := X86_64.withStackArgScratch_spSafe (streamVerify_spSafe v)
    features := (v.ctr.features ++ v.gh.features).dedup }]

end VG.Generic.AesCtr32.Ghash.X86_64.AesGcm
