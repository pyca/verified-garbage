module

public import VerifiedGarbage.Proof.AesSiv.X86.Verified
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
public import VerifiedGarbage.Proof.AesCcm.Mac
public import VerifiedGarbage.Proof.AesGcm.X86.CryptHead
public import VerifiedGarbage.Proof.AesGcm.X86.CryptTail
public import VerifiedGarbage.Proof.AesGcm.X86.CryptWhole
public import VerifiedGarbage.Proof.AesGcm.X86.Flush
public import VerifiedGarbage.Proof.AesGcm.X86.Top
public import VerifiedGarbage.Proof.AesSiv.X86.Dec
public import VerifiedGarbage.Proof.AesSiv.X86.FinRaw
public import VerifiedGarbage.Proof.AesSiv.X86.Finish
public import VerifiedGarbage.Proof.AesSiv.X86.FinishCT
public import VerifiedGarbage.Proof.AesSiv.X86.FinishLong
public import VerifiedGarbage.Proof.AesSiv.X86.Init
public import VerifiedGarbage.Proof.AesSiv.X86.Run
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
import VerifiedGarbage.Proof.AesCcm.Mac
import VerifiedGarbage.Proof.AesGcm.X86.CryptHead
import VerifiedGarbage.Proof.AesGcm.X86.CryptTail
import VerifiedGarbage.Proof.AesGcm.X86.CryptWhole
import VerifiedGarbage.Proof.AesGcm.X86.Flush
import VerifiedGarbage.Proof.AesGcm.X86.Top
import VerifiedGarbage.Proof.AesSiv.X86.Dec
import VerifiedGarbage.Proof.AesSiv.X86.FinRaw
import VerifiedGarbage.Proof.AesSiv.X86.Finish
import VerifiedGarbage.Proof.AesSiv.X86.FinishCT
import VerifiedGarbage.Proof.AesSiv.X86.FinishLong
import VerifiedGarbage.Proof.AesSiv.X86.Init
import VerifiedGarbage.Proof.AesSiv.X86.Run
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
# AES-SIV (RFC 5297) on x86

A generic file (see `TCB/Emit.lean`): the artifacts it lists, calling an
implementation `v` of `vg_aes_ctr32` (through the CMAC functions made with
it, and directly for CTR), are emitted once for each implementation
(`Variants/AesCtr32/X86/`), named with its suffix (e.g.
`vg_aes_siv_encrypt_aesni`), and need its CPU features.

`init` keeps its working space in a frame of 2580 bytes holding a copy of
its three stack arguments (`Proof/AesSiv/X86/Verified.lean`), below which
its calls use 48 bytes; 2628 bytes in all. `encrypt` and `decrypt` keep
theirs in a frame of 2612 bytes holding a copy of their seven stack
arguments, below which they use 56 bytes (a call of a CMAC function, its six
arguments and return address, and its own calls of `vg_aes_ctr32`); 2668
bytes in all.
-/

@[expose] public section

namespace VG.Generic.AesCtr32.X86.AesSiv

open VG.Proof.AesSiv.X86

def artifacts (v : Proof.Aes.X86.Ctr32Impl) : List Artifact := [
  Spec.Siv.initApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86.withStackScratch 2580 3 (Impl.AesSiv.X86.initCore v.expand v.callee v.suffix)
    stack := 2628
    verified := init_framed v
    spSafe := Proof.CmacAes.Stream.X86.withStackScratch_spSafe (init_spSafe v)
    features := v.features },
  Spec.Siv.encryptApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86.withStackScratch 2612 7 (Impl.AesSiv.X86.encrypt v.callee v.suffix)
    stack := 2668
    verified := encrypt_framed v
    spSafe := Proof.CmacAes.Stream.X86.withStackScratch_spSafe (encrypt_spSafe v)
    features := v.features },
  Spec.Siv.decryptApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86.withStackScratch 2612 7 (Impl.AesSiv.X86.decrypt v.callee v.suffix)
    stack := 2668
    verified := decrypt_framed v
    spSafe := Proof.CmacAes.Stream.X86.withStackScratch_spSafe (decrypt_spSafe v)
    features := v.features }]

end VG.Generic.AesCtr32.X86.AesSiv
