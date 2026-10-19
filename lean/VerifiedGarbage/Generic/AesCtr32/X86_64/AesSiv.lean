module

public import VerifiedGarbage.Proof.AesSiv.X86_64.Frame
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.Registration
import VerifiedGarbage.Impl.AesCcm.X86_64
import VerifiedGarbage.Impl.Gcm.X86_64
import VerifiedGarbage.Impl.Gcm.X86_64.Pclmul
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.ExpandKey
import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Rounds
import VerifiedGarbage.Proof.AesCcm.Mac
import VerifiedGarbage.Proof.AesCcm.X86_64.Contract
import VerifiedGarbage.Proof.AesSiv.Ctr32
import VerifiedGarbage.Proof.AesSiv.X86_64.CmacOf
import VerifiedGarbage.Proof.AesSiv.X86_64.Init
import VerifiedGarbage.Proof.AesSiv.X86_64.Open
import VerifiedGarbage.Proof.AesSiv.X86_64.XorBytes
import VerifiedGarbage.Proof.Cmac.Dbl32
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.CmacAes.X86_64.Dbl
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
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
import VerifiedGarbage.Proof.Gcm.Spec
import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Gcm.X86_64.Bits
import VerifiedGarbage.Spec.Ccm.Contract
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch

/-!
# AES-SIV (RFC 5297) key setup on x86-64

A generic file (see `TCB/Emit.lean`): `vg_aes_siv_init`, calling an
implementation `v` of `vg_aes_ctr32` (through the CMAC subkeys made with it)
and the implementation of `vg_aes_expand_key_scratch` that goes with it, is
emitted once for each implementation (`Variants/AesCtr32/X86_64/`), named
with its suffix (e.g. `vg_aes_siv_init_aesni`), and needs its CPU features.
`vg_aes_siv_encrypt` and `vg_aes_siv_decrypt`, which also call
`vg_cmac_aes_update`, follow its implementations instead
(`Generic/CmacAesUpdate/X86_64/AesSiv.lean`).

`init` keeps its working space in a frame of its own
(`Proof/AesSiv/X86_64/Frame.lean`) of 2568 bytes, below which its calls use
16 bytes: the return addresses of the call of `vg_cmac_aes_subkeys` (or of
`vg_aes_expand_key_scratch`) and of its call of `vg_aes_ctr32` (2584 bytes
of stack in all).
-/

@[expose] public section

namespace VG.Generic.AesCtr32.X86_64.AesSiv

open VG.Proof.AesSiv.X86_64

def artifacts (v : Proof.Aes.X86_64.Ctr32Impl) : List Artifact := [
  Spec.Siv.initApi.artifact X86_64.target {
    suffix := v.suffix
    notes := [
      "This implementation expands the keys with `" ++ v.expand.name ++ "` and computes the CMAC subkeys \
      with `" ++ Spec.Cmac.aesSubkeysApi.name ++ v.suffix ++ "`."]
    code := Impl.StackScratch.X86_64.withStackScratch 2568 .rcx
      (Impl.AesSiv.X86_64.init v.expand v.callee v.suffix)
    stack := 2584
    verified := init_framed v
    spSafe := X86_64.withStackScratch_spSafe_of (init_spSafe v)
    features := v.features }]

end VG.Generic.AesCtr32.X86_64.AesSiv
