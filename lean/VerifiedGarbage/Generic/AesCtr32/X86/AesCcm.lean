module

public import VerifiedGarbage.Proof.AesCcm.X86.Frame
import VerifiedGarbage.Proof.CmacAes.Stream.X86.Frame
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Cmac.Contract
public import VerifiedGarbage.Proof.CmacAes.Stream.X86.Frame
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyRecurrence
public import VerifiedGarbage.Proof.Aes.X86.AesNi.Load
public import VerifiedGarbage.Proof.Aes.X86.AesNi.Prologue
public import VerifiedGarbage.Proof.Aes.X86.AesNi.Restore
public import VerifiedGarbage.Proof.Aes.X86.AesNi.Tail
public import VerifiedGarbage.Proof.AesCcm.X86.Aad
public import VerifiedGarbage.Proof.AesCcm.X86.AadCT
public import VerifiedGarbage.Proof.AesCcm.X86.Blocks
public import VerifiedGarbage.Proof.AesCcm.X86.Entry
public import VerifiedGarbage.Proof.AesCcm.X86.Mac
public import VerifiedGarbage.Proof.AesCcm.X86.Run
public import VerifiedGarbage.Proof.AesCcm.X86.SealCT
public import VerifiedGarbage.Proof.AesGcm.X86.CryptHead
public import VerifiedGarbage.Proof.AesGcm.X86.CryptTail
public import VerifiedGarbage.Proof.AesGcm.X86.CryptWhole
public import VerifiedGarbage.Proof.AesGcm.X86.Flush
public import VerifiedGarbage.Proof.AesGcm.X86.Top
public import VerifiedGarbage.Proof.Cmac.Frame
public import VerifiedGarbage.Proof.Cmac.Mem
public import VerifiedGarbage.Proof.Cmac.Spec
public import VerifiedGarbage.Proof.CmacAes.Stream.X86.Absorb
public import VerifiedGarbage.Proof.CmacAes.X86.UpdateCT
public import VerifiedGarbage.Proof.CmacAes.X86.UpdateCorrect
public import VerifiedGarbage.Proof.CmacAes.X86.Verified
public import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Framework.X86.SseTaint
public import VerifiedGarbage.Proof.Framework.X86.StackScratch
public import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyRecurrence
import VerifiedGarbage.Proof.Aes.X86.AesNi.Load
import VerifiedGarbage.Proof.Aes.X86.AesNi.Prologue
import VerifiedGarbage.Proof.Aes.X86.AesNi.Restore
import VerifiedGarbage.Proof.Aes.X86.AesNi.Tail
import VerifiedGarbage.Proof.AesCcm.X86.Aad
import VerifiedGarbage.Proof.AesCcm.X86.AadCT
import VerifiedGarbage.Proof.AesCcm.X86.Blocks
import VerifiedGarbage.Proof.AesCcm.X86.Entry
import VerifiedGarbage.Proof.AesCcm.X86.Mac
import VerifiedGarbage.Proof.AesCcm.X86.Run
import VerifiedGarbage.Proof.AesCcm.X86.SealCT
import VerifiedGarbage.Proof.AesGcm.X86.CryptHead
import VerifiedGarbage.Proof.AesGcm.X86.CryptTail
import VerifiedGarbage.Proof.AesGcm.X86.CryptWhole
import VerifiedGarbage.Proof.AesGcm.X86.Flush
import VerifiedGarbage.Proof.AesGcm.X86.Top
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.CmacAes.Stream.X86.Absorb
import VerifiedGarbage.Proof.CmacAes.X86.UpdateCT
import VerifiedGarbage.Proof.CmacAes.X86.UpdateCorrect
import VerifiedGarbage.Proof.CmacAes.X86.Verified
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.X86.StackScratch
import VerifiedGarbage.Proof.Sha256.Stream

/-!
# AES-CCM (NIST SP 800-38C) on x86

A generic file (see `TCB/Emit.lean`): the artifacts it lists, calling an
implementation `v` of `vg_aes_ctr32` (through `vg_cmac_aes_update` made with
it, for the CBC-MAC, and directly for counter mode), are emitted once for
each implementation (`Variants/AesCtr32/X86/`), named with its suffix
(e.g. `vg_aes_ccm_seal_aesni`), and need its CPU features.

Each runs in a frame of 2608 bytes holding its working space and a copy of
its ten stack arguments (`Proof/AesCcm/X86/Frame.lean`), below which it uses
56 bytes: a call of `vg_cmac_aes_update` (its six arguments and return
address) and its own calls of `vg_aes_ctr32`; 2664 bytes in all.
-/

@[expose] public section

namespace VG.Generic.AesCtr32.X86.AesCcm

open VG.Proof.AesCcm.X86

def artifacts (v : Proof.Aes.X86.Ctr32Impl) : List Artifact := [
  Spec.Ccm.sealApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86.withStackScratch 2608 10 (Impl.AesCcm.X86.seal v.callee v.suffix)
    stack := 2664
    verified := seal_framed v
    spSafe := Proof.CmacAes.Stream.X86.withStackScratch_spSafe (seal_spSafe v)
    features := v.features },
  Spec.Ccm.openApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86.withStackScratch 2608 10 (Impl.AesCcm.X86.open v.callee v.suffix)
    stack := 2664
    verified := open_framed v
    spSafe := Proof.CmacAes.Stream.X86.withStackScratch_spSafe (open_spSafe v)
    features := v.features }]

end VG.Generic.AesCtr32.X86.AesCcm
