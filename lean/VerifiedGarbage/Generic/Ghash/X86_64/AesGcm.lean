module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Instances
public import VerifiedGarbage.Proof.Aes.X86_64.Variant
public import VerifiedGarbage.Proof.AesGcm.X86_64.GhashImpls
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
public import VerifiedGarbage.TCB.X86_64.Print

/-! # AES-GCM's GHASH-only functions on x86-64 -/

@[expose] public section

namespace VG.Generic.Ghash.X86_64.AesGcm

open VG.Proof.AesGcm.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)

/-- The artifacts calling the implementation `n` of `vg_ghash`, and no AES. -/
def artifacts (n : GhashName) : List Artifact :=
  let v : GcmImpl := { ctr := Ctr32Impl.scalar, key := KeyImpl.scalar, gh := n.impl }
  [
  Spec.Gcm.streamInitApi.artifact X86_64.target {
    select := true
    suffix := n.impl.suffix
    code := Impl.StackScratch.X86_64.withStackScratch 2568 .r8
      (Impl.AesGcm.X86_64.streamInit v.callees)
    stack := 2576
    verified := streamInit_framed v
    spSafe := X86_64.withStackScratch_spSafe_of (streamInit_spSafe v)
    features := v.gh.features },
  Spec.Gcm.streamAadApi.artifact X86_64.target {
    select := true
    suffix := n.impl.suffix
    code := Impl.StackScratch.X86_64.withStackScratch 2568 .r9
      (Impl.AesGcm.X86_64.streamAad v.callees)
    stack := 2576
    verified := streamAad_framed v
    spSafe := X86_64.withStackScratch_spSafe_of (streamAad_spSafe v)
    features := v.gh.features }]

end VG.Generic.Ghash.X86_64.AesGcm
