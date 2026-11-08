module

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

/-! # AES-GCM's AES-only function on x86: `vg_aes_gcm_init` -/

@[expose] public section

namespace VG.Generic.AesCtr32.X86.AesGcm

open VG.Proof.AesGcm.X86

/-- The artifacts calling the implementation `c` of `vg_aes_ctr32_to`, and no GHASH. -/
def artifacts (c : Proof.Aes.X86.Ctr32Impl) : List Artifact :=
  let v : GcmImpl := { ctr := c, gh := GhashName.scalar.impl }
  [
  Spec.Gcm.initApi.artifact X86.target {
    suffix := c.suffix
    code := Impl.StackScratch.X86.withStackScratch 2580 3 (Impl.AesGcm.X86.init v.callees)
    stack := 2612
    verified := init_framed v
    spSafe := withStackScratch_spSafe (init_spSafe v)
    features := (v.ctr.features) }]

end VG.Generic.AesCtr32.X86.AesGcm
