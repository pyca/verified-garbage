module

public import VerifiedGarbage.Proof.AesSiv.AArch64.Frame
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.AesCcm.Mac
public import VerifiedGarbage.Proof.AesSiv.AArch64.Call
public import VerifiedGarbage.Proof.AesSiv.AArch64.Finish
public import VerifiedGarbage.Proof.AesSiv.AArch64.FinishLong
public import VerifiedGarbage.Proof.AesSiv.AArch64.Open
public import VerifiedGarbage.Proof.AesSiv.AArch64.S2vAd
public import VerifiedGarbage.Proof.AesSiv.Ctr32
public import VerifiedGarbage.Proof.AesSiv.Key
public import VerifiedGarbage.Proof.Cmac.Dbl32
public import VerifiedGarbage.Proof.Cmac.Spec
public import VerifiedGarbage.Proof.CmacAes.AArch64.UpdateCorrect
public import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.Framework.AArch64.RelCT
public import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.AesCcm.Mac
import VerifiedGarbage.Proof.AesSiv.AArch64.Call
import VerifiedGarbage.Proof.AesSiv.AArch64.Finish
import VerifiedGarbage.Proof.AesSiv.AArch64.FinishLong
import VerifiedGarbage.Proof.AesSiv.AArch64.Open
import VerifiedGarbage.Proof.AesSiv.AArch64.S2vAd
import VerifiedGarbage.Proof.AesSiv.Ctr32
import VerifiedGarbage.Proof.AesSiv.Key
import VerifiedGarbage.Proof.Cmac.Dbl32
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.CmacAes.AArch64.UpdateCorrect
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Gcm.Stream

/-!
# AES-SIV (RFC 5297) key setup on AArch64

A generic file (see `TCB/Emit.lean`): `vg_aes_siv_init`, calling an
implementation `v` of `vg_aes_ctr32` (through the CMAC subkeys made with it)
and the implementation of `vg_aes_expand_key_scratch` that goes with it, is emitted
once for each implementation (`Variants/AesCtr32/AArch64/`), named with its
suffix (e.g. `vg_aes_siv_init_aes`), and needs its CPU features.
`vg_aes_siv_encrypt` and `vg_aes_siv_decrypt`, which also call
`vg_cmac_aes_update`, follow its implementations instead
(`Generic/CmacAesUpdate/AArch64/AesSiv.lean`).

`init` keeps its working space in a frame of its own
(`Proof/AesSiv/AArch64/Frame.lean`): its `stack` is that frame. Its calls
(`bl`) keep the return address in `x30`, which it saves in the working space.
-/

@[expose] public section

namespace VG.Generic.AesCtr32.AArch64.AesSiv

open VG.Proof.AesSiv.AArch64

def artifacts (v : Proof.Aes.AArch64.Ctr32Impl) : List Artifact := [
  Spec.Siv.initApi.artifact AArch64.target {
    suffix := v.suffix
    notes := [
      "This implementation expands the keys with `" ++ v.expand.name ++ "` and computes the CMAC subkeys \
      with `" ++ Spec.Cmac.aesSubkeysApi.name ++ v.suffix ++ "`."]
    code := Impl.StackScratch.AArch64.withStackScratch 2560 .x3
      (Impl.AesSiv.AArch64.init v.expand v.callee v.suffix)
    stack := 2560
    verified := init_framed v
    features := v.features }]

end VG.Generic.AesCtr32.AArch64.AesSiv
