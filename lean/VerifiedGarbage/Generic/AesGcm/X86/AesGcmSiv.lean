module

public import VerifiedGarbage.Proof.AesGcmSiv.X86.Frame
public import VerifiedGarbage.Proof.GcmSiv.Polyval
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.AesGcm.X86.GhashImpls
public import VerifiedGarbage.Proof.AesGcm.X86.Verified
import VerifiedGarbage.Proof.AesGcm.X86.Frame
public import VerifiedGarbage.Proof.AesGcm.X86.Frame
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Generic.AesGcm.X86.AesGcm
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
public import VerifiedGarbage.Proof.AesGcmSiv.X86.Cmp
public import VerifiedGarbage.Proof.AesGcmSiv.X86.Derive
public import VerifiedGarbage.Proof.AesGcmSiv.X86.FnCT
public import VerifiedGarbage.Proof.AesGcmSiv.X86.Open
public import VerifiedGarbage.Proof.AesGcmSiv.X86.Polyval
public import VerifiedGarbage.Proof.AesGcmSiv.X86.Run
public import VerifiedGarbage.Proof.AesGcmSiv.X86.TagIO
public import VerifiedGarbage.Proof.Cmac.Block
public import VerifiedGarbage.Proof.Cmac.Frame
public import VerifiedGarbage.Proof.Cmac.Spec
public import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Framework.X86.SseTaint
public import VerifiedGarbage.Proof.Framework.X86.StackScratch
public import VerifiedGarbage.Proof.Gcm.Be64
public import VerifiedGarbage.Proof.Gcm.Bits
public import VerifiedGarbage.Proof.Gcm.SealGather
public import VerifiedGarbage.Proof.GcmSiv.Words32
public import VerifiedGarbage.Proof.Siv.Spec
import VerifiedGarbage.Generic.AesGcm.X86.AesGcm
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
import VerifiedGarbage.Proof.AesGcmSiv.X86.Cmp
import VerifiedGarbage.Proof.AesGcmSiv.X86.Derive
import VerifiedGarbage.Proof.AesGcmSiv.X86.FnCT
import VerifiedGarbage.Proof.AesGcmSiv.X86.Open
import VerifiedGarbage.Proof.AesGcmSiv.X86.Polyval
import VerifiedGarbage.Proof.AesGcmSiv.X86.Run
import VerifiedGarbage.Proof.AesGcmSiv.X86.TagIO
import VerifiedGarbage.Proof.Cmac.Block
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.X86.StackScratch
import VerifiedGarbage.Proof.Gcm.Be64
import VerifiedGarbage.Proof.Gcm.Bits
import VerifiedGarbage.Proof.Gcm.SealGather
import VerifiedGarbage.Proof.GcmSiv.Words32
import VerifiedGarbage.Proof.Siv.Spec

/-!
# AES-GCM-SIV (RFC 8452) on x86

A generic file (see `TCB/Emit.lean`): the artifacts it lists, calling the
implementations `v` of `vg_aes_ctr32`, `vg_aes_expand_key` and `vg_ghash`
(those of AES-GCM), are emitted once for each combination
(`Variants/AesGcm/X86/`), named with its suffix (e.g.
`vg_aes_gcm_siv_seal_aesni_pclmul`), and need the CPU features of the three.

Each runs in a frame of 2856 bytes holding its working space and a copy of
its eight stack arguments (`Proof/AesGcmSiv/X86/Frame.lean`), below which it
uses 28 bytes: a call of `vg_aes_ctr32` (six arguments and the return
address; the calls of the other two push fewer), which makes no calls;
2884 bytes in all. The proofs take the tag input computed with GHASH to be
RFC 8452's (`Proof.GcmSiv.Polyval.tagInput_eq_tagInputG`), which this file
imports, with its algebra, so that the proofs need not.
-/

@[expose] public section

namespace VG.Generic.AesGcm.X86.AesGcmSiv

open VG.Proof.AesGcm.X86 (GcmImpl GcmVariant)
open VG.Proof.AesGcmSiv.X86

/-- The artifacts calling the implementations `v`. -/
def artifactsOf (v : GcmImpl) : List Artifact := [
  Spec.GcmSiv.sealApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86.withStackScratch 2856 8 (Impl.AesGcmSiv.X86.«seal» v.callees)
    stack := 2884
    verified := seal_framed v VG.Proof.GcmSiv.Polyval.tagInput_eq_tagInputG
    spSafe := Proof.AesGcm.X86.withStackScratch_spSafe (seal_spSafe v)
    features := v.features },
  Spec.GcmSiv.openApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86.withStackScratch 2856 8 (Impl.AesGcmSiv.X86.«open» v.callees)
    stack := 2884
    verified := open_framed v VG.Proof.GcmSiv.Polyval.tagInput_eq_tagInputG
    spSafe := Proof.AesGcm.X86.withStackScratch_spSafe (open_spSafe v)
    features := v.features }]

/-- The artifacts of a variant, from the implementations it names. -/
def artifacts (v : GcmVariant) : List Artifact := artifactsOf v.impl

end VG.Generic.AesGcm.X86.AesGcmSiv
