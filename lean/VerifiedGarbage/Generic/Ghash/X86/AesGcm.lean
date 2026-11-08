module

public import VerifiedGarbage.Proof.Aes.X86.VariantProof
public import VerifiedGarbage.Proof.AesGcm.X86.GhashImpls
public import VerifiedGarbage.Proof.AesGcm.X86.Gather.Verified
public import VerifiedGarbage.Proof.AesGcm.X86.OpenTo.Verified
public import VerifiedGarbage.Proof.AesGcm.RoundsTo
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyRecurrence
public import VerifiedGarbage.Proof.Aes.X86.AesNi.Load
public import VerifiedGarbage.Proof.Aes.X86.AesNi.Prologue
public import VerifiedGarbage.Proof.Aes.X86.AesNi.Restore
public import VerifiedGarbage.Proof.Aes.X86.AesNi.Tail
public import VerifiedGarbage.Proof.AesGcm.X86.CryptHead
public import VerifiedGarbage.Proof.AesGcm.X86.CryptTail
public import VerifiedGarbage.Proof.AesGcm.X86.CryptWhole
public import VerifiedGarbage.Proof.AesGcm.X86.Flush
public import VerifiedGarbage.Proof.AesGcm.X86.Gather.CT
public import VerifiedGarbage.Proof.AesGcm.X86.Gather.Fn
public import VerifiedGarbage.Proof.AesGcm.X86.Init
public import VerifiedGarbage.Proof.Cmac.Frame
public import VerifiedGarbage.Proof.Cmac.Mem
public import VerifiedGarbage.Proof.Cmac.Spec
public import VerifiedGarbage.Proof.Framework.X86.SseTaint
public import VerifiedGarbage.Proof.Framework.X86.StackScratch
public import VerifiedGarbage.Proof.Gcm.SealGather
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyRecurrence
import VerifiedGarbage.Proof.Aes.X86.AesNi.Load
import VerifiedGarbage.Proof.Aes.X86.AesNi.Prologue
import VerifiedGarbage.Proof.Aes.X86.AesNi.Restore
import VerifiedGarbage.Proof.Aes.X86.AesNi.Tail
import VerifiedGarbage.Proof.AesGcm.X86.CryptHead
import VerifiedGarbage.Proof.AesGcm.X86.CryptTail
import VerifiedGarbage.Proof.AesGcm.X86.CryptWhole
import VerifiedGarbage.Proof.AesGcm.X86.Flush
import VerifiedGarbage.Proof.AesGcm.X86.Gather.CT
import VerifiedGarbage.Proof.AesGcm.X86.Gather.Fn
import VerifiedGarbage.Proof.AesGcm.X86.Init
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.X86.StackScratch
import VerifiedGarbage.Proof.Gcm.SealGather

/-! # AES-GCM's GHASH-only functions on x86 -/

@[expose] public section

namespace VG.Generic.Ghash.X86.AesGcm

open VG.Proof.AesGcm.X86

/-- The artifacts calling the implementation `n` of `vg_ghash`, and no AES. -/
def artifacts (n : GhashName) : List Artifact :=
  let v : GcmImpl := { ctr := Proof.Aes.X86.Ctr32Impl.scalar, gh := n.impl }
  [
  Spec.Gcm.streamAadApi.artifact X86.target {
    select := true
    suffix := n.impl.suffix
    code := Impl.StackScratch.X86.withStackScratch 2592 6 (Impl.AesGcm.X86.streamAad v.callees)
    stack := 2616
    verified := streamAad_framed v
    spSafe := withStackScratch_spSafe (streamAad_spSafe v)
    features := v.gh.features },
  Spec.Gcm.streamInitApi.artifact X86.target {
    select := true
    suffix := n.impl.suffix
    code := Impl.StackScratch.X86.withStackScratch 2584 4 (Impl.AesGcm.X86.streamInit v.callees)
    stack := 2608
    verified := streamInit_framed v
    spSafe := withStackScratch_spSafe (streamInit_spSafe v)
    features := v.gh.features }]

end VG.Generic.Ghash.X86.AesGcm
