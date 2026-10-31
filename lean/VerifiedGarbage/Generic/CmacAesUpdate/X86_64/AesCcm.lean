module

public import VerifiedGarbage.Proof.AesCcm.X86_64.Frame
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
public import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
public import VerifiedGarbage.Impl.CmacAes.Stream.X86_64
public import VerifiedGarbage.Impl.Gcm.X86_64
public import VerifiedGarbage.Impl.Gcm.X86_64.Pclmul
public import VerifiedGarbage.Proof.Aes.X86_64.AesNi.ExpandKey
public import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Rounds
public import VerifiedGarbage.Proof.AesCcm.X86_64.Blocks
public import VerifiedGarbage.Proof.AesCcm.X86_64.Bytes
public import VerifiedGarbage.Proof.AesCcm.X86_64.Crypt
public import VerifiedGarbage.Proof.AesCcm.X86_64.CryptCT
public import VerifiedGarbage.Proof.AesCcm.X86_64.Ctrs
public import VerifiedGarbage.Proof.AesCcm.X86_64.Header
public import VerifiedGarbage.Proof.AesCcm.X86_64.Mac
public import VerifiedGarbage.Proof.AesCcm.X86_64.OpenCT
public import VerifiedGarbage.Proof.AesCcm.X86_64.Run
public import VerifiedGarbage.Proof.AesCcm.X86_64.Seal
public import VerifiedGarbage.Proof.AesCcm.X86_64.Tag
public import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
public import VerifiedGarbage.Proof.Cmac.Frame
public import VerifiedGarbage.Proof.Cmac.Spec
public import VerifiedGarbage.Proof.Cmac.Stream
public import VerifiedGarbage.Proof.CmacAes.X86_64.Dbl
public import VerifiedGarbage.Proof.CmacAes.X86_64.Finalize
public import VerifiedGarbage.Proof.CmacAes.X86_64.FinalizeCorrect
public import VerifiedGarbage.Proof.CmacAes.X86_64.UpdateCorrect
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.OffsetBelow
public import VerifiedGarbage.Proof.Framework.Range
public import VerifiedGarbage.Proof.Framework.RegSetOrder
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Framework.X86_64.Avx
public import VerifiedGarbage.Proof.Framework.X86_64.Bswap
public import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
public import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Proof.Framework.X86_64.Masked
public import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
public import VerifiedGarbage.Proof.Framework.X86_64.RelCT
public import VerifiedGarbage.Proof.Framework.X86_64.Sse
public import VerifiedGarbage.Proof.Gcm.Bits
public import VerifiedGarbage.Proof.Gcm.Spec
public import VerifiedGarbage.Proof.Gcm.Stream
public import VerifiedGarbage.Proof.Gcm.X86_64.Bits
import VerifiedGarbage.Impl.CmacAes.Stream.X86_64
import VerifiedGarbage.Impl.Gcm.X86_64
import VerifiedGarbage.Impl.Gcm.X86_64.Pclmul
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.ExpandKey
import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Rounds
import VerifiedGarbage.Proof.AesCcm.X86_64.Blocks
import VerifiedGarbage.Proof.AesCcm.X86_64.Bytes
import VerifiedGarbage.Proof.AesCcm.X86_64.Crypt
import VerifiedGarbage.Proof.AesCcm.X86_64.CryptCT
import VerifiedGarbage.Proof.AesCcm.X86_64.Ctrs
import VerifiedGarbage.Proof.AesCcm.X86_64.Header
import VerifiedGarbage.Proof.AesCcm.X86_64.Mac
import VerifiedGarbage.Proof.AesCcm.X86_64.OpenCT
import VerifiedGarbage.Proof.AesCcm.X86_64.Run
import VerifiedGarbage.Proof.AesCcm.X86_64.Seal
import VerifiedGarbage.Proof.AesCcm.X86_64.Tag
import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.CmacAes.X86_64.Dbl
import VerifiedGarbage.Proof.CmacAes.X86_64.Finalize
import VerifiedGarbage.Proof.CmacAes.X86_64.FinalizeCorrect
import VerifiedGarbage.Proof.CmacAes.X86_64.UpdateCorrect
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Bswap
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Gcm.Bits
import VerifiedGarbage.Proof.Gcm.Spec
import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Gcm.X86_64.Bits

/-!
# AES-CCM (NIST SP 800-38C) on x86-64

A generic file (see `TCB/Emit.lean`): the artifacts it lists, calling an
implementation `v` of `vg_cmac_aes_update` for the CBC-MAC, and the
implementation of `vg_aes_ctr32` that goes with it (`v.ctr`) for counter
mode, are emitted once for each implementation
(`Variants/CmacAesUpdate/X86_64/`), named with its suffix (e.g.
`vg_aes_ccm_seal_aesni_cbc`), and need the CPU features of both.

The code of each uses at most 16 bytes of stack: the return addresses of
the call of `vg_cmac_aes_update` (or of `vg_aes_ctr32`) and of its call of
`vg_aes_ctr32`, if it makes one; both also read their arguments after the
sixth, from the data to the tag's length, from the stack above their return
address. Each keeps its working space, its last argument, in a frame of
2608 bytes on the stack that also holds a copy of its four other stack
arguments (`Verified.stackArgScratch`).
-/

@[expose] public section

namespace VG.Generic.CmacAesUpdate.X86_64.AesCcm

open VG.Proof.AesCcm.X86_64

def artifacts (v : Proof.CmacAes.X86_64.UpdateImpl) : List Artifact := [
  Spec.Ccm.sealApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 2608 4 (Impl.AesCcm.X86_64.seal v.callee v.ctr.callee)
    stack := 2624
    verified := seal_framed v
    spSafe := X86_64.withStackArgScratch_spSafe (seal_spSafe v)
    features := v.ctr.features },
  Spec.Ccm.openApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 2608 4 (Impl.AesCcm.X86_64.open v.callee v.ctr.callee)
    stack := 2624
    verified := open_framed v
    spSafe := X86_64.withStackArgScratch_spSafe (open_spSafe v)
    features := v.ctr.features }]

end VG.Generic.CmacAesUpdate.X86_64.AesCcm
