module

public import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Frame
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.X86_64.Registration
import VerifiedGarbage.Impl.Gcm.X86_64
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.ExpandKey
import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Rounds
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Copy
import VerifiedGarbage.Proof.CmacAes.X86_64.Dbl
import VerifiedGarbage.Proof.CmacAes.X86_64.Finalize
import VerifiedGarbage.Proof.CmacAes.X86_64.UpdateCorrect
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Gcm.Spec
import VerifiedGarbage.Proof.Gcm.X86_64.Bits

/-!
# Streaming AES-CMAC's `absorb` on x86-64

A generic file (see `TCB/Emit.lean`): `vg_cmac_aes_absorb`, calling an
implementation `v` of `vg_cmac_aes_update`, is emitted once for each
implementation (`Variants/CmacAesUpdate/X86_64/`), named with its suffix
(e.g. `vg_cmac_aes_absorb_aesni_cbc`), and needs its CPU features. Its
buffering proof depends on the update's contract, not on how it chains.

It keeps its working space in a frame of its own on the stack
(`Proof/CmacAes/Stream/X86_64/Frame.lean`), below which its calls use at
most 16 bytes: the return addresses of the call of `vg_cmac_aes_update` and
of its call of `vg_aes_ctr32`.
-/

@[expose] public section

namespace VG.Generic.CmacAesUpdate.X86_64.Absorb

def artifacts (v : Proof.CmacAes.X86_64.UpdateImpl) : List Artifact := [
  Spec.Cmac.aesAbsorbApi.artifact X86_64.target {
    suffix := v.suffix
    notes := [
      "This implementation chains blocks with `" ++ v.callee.name ++ "`."]
    code := Impl.StackScratch.X86_64.withStackScratch 2312 .r9 (Impl.CmacAes.Stream.X86_64.absorb v.callee)
    stack := 2328
    verified := Proof.CmacAes.Stream.X86_64.absorb_framed v
    spSafe := X86_64.withStackScratch_spSafe_of (Proof.CmacAes.Stream.X86_64.absorb_spSafe v)
    features := v.features }]

end VG.Generic.CmacAesUpdate.X86_64.Absorb
