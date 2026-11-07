module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Instances
public import VerifiedGarbage.Proof.Aes.X86_64.Variant
public import VerifiedGarbage.Proof.AesGcm.X86_64.GhashImpls
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
public import VerifiedGarbage.TCB.X86_64.Print

/-! # AES-GCM's AES-only function on x86-64: `vg_aes_gcm_init` -/

@[expose] public section

namespace VG.Generic.AesCtr32.X86_64.AesGcm

open VG.Proof.AesGcm.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)

/-- The artifacts calling the implementation `c` of `vg_aes_ctr32`, with the
key expansion for the same CPUs, and no GHASH. -/
def artifacts (c : Ctr32Impl) : List Artifact :=
  let v : GcmImpl :=
    { ctr := c, key := if c.features.isEmpty then KeyImpl.scalar else KeyImpl.aesni,
      gh := GhashName.scalar.impl }
  [
  Spec.Gcm.initApi.artifact X86_64.target {
    suffix := c.suffix
    code := Impl.StackScratch.X86_64.withStackScratch 2568 .rcx (Impl.AesGcm.X86_64.init v.callees)
    stack := 2576
    verified := init_framed v
    spSafe := X86_64.withStackScratch_spSafe_of (init_spSafe v)
    features := (v.ctr.features ++ v.key.features).dedup }]

end VG.Generic.AesCtr32.X86_64.AesGcm
