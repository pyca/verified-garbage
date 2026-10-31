module

public import VerifiedGarbage.Proof.AesOcb.X86.Frame
import VerifiedGarbage.Proof.CmacAes.Stream.X86.Frame
public import VerifiedGarbage.Proof.Framework.Registration
public import Mathlib.Tactic.Conv
public import VerifiedGarbage.Proof.CmacAes.Stream.X86.Frame
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Aes.X86.AesNi.BlocksLoop
public import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyRecurrence
public import VerifiedGarbage.Proof.Aes.X86.AesNi.Load
public import VerifiedGarbage.Proof.Aes.X86.AesNi.Prologue
public import VerifiedGarbage.Proof.Aes.X86.AesNi.Restore
public import VerifiedGarbage.Proof.Aes.X86.AesNi.Tail
public import VerifiedGarbage.Proof.Aes.X86.Decrypt
public import VerifiedGarbage.Proof.AesGcm.X86.CryptHead
public import VerifiedGarbage.Proof.AesGcm.X86.CryptTail
public import VerifiedGarbage.Proof.AesGcm.X86.CryptWhole
public import VerifiedGarbage.Proof.AesGcm.X86.Flush
public import VerifiedGarbage.Proof.AesOcb.X86.Blk
public import VerifiedGarbage.Proof.AesOcb.X86.Calls
public import VerifiedGarbage.Proof.AesOcb.X86.Entry
public import VerifiedGarbage.Proof.AesOcb.X86.Init
public import VerifiedGarbage.Proof.AesOcb.X86.LNtz
public import VerifiedGarbage.Proof.AesOcb.X86.NonceBlock
public import VerifiedGarbage.Proof.AesOcb.X86.Offset0
public import VerifiedGarbage.Proof.AesOcb.X86.Run
public import VerifiedGarbage.Proof.AesOcb.X86.Setup
public import VerifiedGarbage.Proof.Cmac.Block
public import VerifiedGarbage.Proof.Cmac.Frame
public import VerifiedGarbage.Proof.Cmac.Spec
public import VerifiedGarbage.Proof.CmacAes.Stream.X86.Absorb
public import VerifiedGarbage.Proof.CmacAes.X86.UpdateCT
public import VerifiedGarbage.Proof.CmacAes.X86.UpdateCorrect
public import VerifiedGarbage.Proof.CmacAes.X86.Verified
public import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Framework.X86.SseTaint
public import VerifiedGarbage.Proof.Framework.X86.StackScratch
public import VerifiedGarbage.Proof.Gcm.Be64
public import VerifiedGarbage.Proof.Gcm.Bits
public import VerifiedGarbage.Proof.Ocb.Spec
public import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Aes.X86.AesNi.BlocksLoop
import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyRecurrence
import VerifiedGarbage.Proof.Aes.X86.AesNi.Load
import VerifiedGarbage.Proof.Aes.X86.AesNi.Prologue
import VerifiedGarbage.Proof.Aes.X86.AesNi.Restore
import VerifiedGarbage.Proof.Aes.X86.AesNi.Tail
import VerifiedGarbage.Proof.Aes.X86.Decrypt
import VerifiedGarbage.Proof.AesGcm.X86.CryptHead
import VerifiedGarbage.Proof.AesGcm.X86.CryptTail
import VerifiedGarbage.Proof.AesGcm.X86.CryptWhole
import VerifiedGarbage.Proof.AesGcm.X86.Flush
import VerifiedGarbage.Proof.AesOcb.X86.Blk
import VerifiedGarbage.Proof.AesOcb.X86.Calls
import VerifiedGarbage.Proof.AesOcb.X86.Entry
import VerifiedGarbage.Proof.AesOcb.X86.Init
import VerifiedGarbage.Proof.AesOcb.X86.LNtz
import VerifiedGarbage.Proof.AesOcb.X86.NonceBlock
import VerifiedGarbage.Proof.AesOcb.X86.Offset0
import VerifiedGarbage.Proof.AesOcb.X86.Run
import VerifiedGarbage.Proof.AesOcb.X86.Setup
import VerifiedGarbage.Proof.Cmac.Block
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.CmacAes.Stream.X86.Absorb
import VerifiedGarbage.Proof.CmacAes.X86.UpdateCT
import VerifiedGarbage.Proof.CmacAes.X86.UpdateCorrect
import VerifiedGarbage.Proof.CmacAes.X86.Verified
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.X86.StackScratch
import VerifiedGarbage.Proof.Gcm.Be64
import VerifiedGarbage.Proof.Gcm.Bits
import VerifiedGarbage.Proof.Ocb.Spec
import VerifiedGarbage.Proof.Sha256.Stream

/-!
# AES-OCB (RFC 7253) on x86

A generic file (see `TCB/Emit.lean`): the artifacts it lists, calling an
implementation `v` of `vg_aes_encrypt_blocks`, `vg_aes_decrypt_blocks` and
`vg_aes_expand_key_scratch`, are emitted once for each implementation
(`Variants/AesBlocks/X86/`), named with its suffix (e.g.
`vg_aes_ocb_seal_aesni`), and need its CPU features.

Each runs in a frame holding its working space and a copy of its stack
arguments (`Proof/AesOcb/X86/Frame.lean`): 2608 bytes for `seal` and `open`
(ten arguments), 2580 bytes for `init` (three), below which its calls use 24
bytes (their five arguments and return address; the callees use no stack).
-/

@[expose] public section

namespace VG.Generic.AesBlocks.X86.AesOcb

open VG.Proof.AesOcb.X86

def artifacts (v : Proof.Aes.X86.BlocksImpl) : List Artifact := [
  Spec.Ocb.initApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86.withStackScratch 2580 3 (Impl.AesOcb.X86.init (callees v))
    stack := 2604
    verified := init_framed v
    spSafe := Proof.CmacAes.Stream.X86.withStackScratch_spSafe (init_spSafe v)
    features := v.features },
  Spec.Ocb.sealApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86.withStackScratch 2608 10 (Impl.AesOcb.X86.seal (callees v))
    stack := 2632
    verified := seal_framed v
    spSafe := Proof.CmacAes.Stream.X86.withStackScratch_spSafe (seal_spSafe v)
    features := v.features },
  Spec.Ocb.openApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86.withStackScratch 2608 10 (Impl.AesOcb.X86.open (callees v))
    stack := 2632
    verified := open_framed v
    spSafe := Proof.CmacAes.Stream.X86.withStackScratch_spSafe (open_spSafe v)
    features := v.features }]

end VG.Generic.AesBlocks.X86.AesOcb
