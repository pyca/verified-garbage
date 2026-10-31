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
# AES-SIV (RFC 5297) encryption and decryption on AArch64

A generic file (see `TCB/Emit.lean`): `vg_aes_siv_encrypt` and
`vg_aes_siv_decrypt`, calling an implementation `v` of `vg_cmac_aes_update`,
and the CMAC functions and `vg_aes_ctr32` made with the implementation of
AES that goes with it (`v.ctr`), are emitted once for each implementation
of the update (`Variants/CmacAesUpdate/AArch64/`), named with its suffix
(e.g. `vg_aes_siv_encrypt_aes_cbc`), and need its CPU features.

Each function keeps its working space, 2576 bytes, in a frame of its own
(`Proof/AesSiv/AArch64/Frame.lean`): its `stack` is that frame. Their calls
(`bl`) keep the return address in `x30`, which they save in the working
space.
-/

@[expose] public section

namespace VG.Generic.CmacAesUpdate.AArch64.AesSiv

open VG.Proof.AesSiv.AArch64

def artifacts (v : Proof.CmacAes.AArch64.UpdateImpl) : List Artifact := [
  Spec.Siv.encryptApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.StackScratch.AArch64.withStackScratch 2576 .x7
      (Impl.AesSiv.AArch64.encrypt v.callee v.ctr.callee v.ctr.suffix)
    stack := 2576
    verified := encrypt_framed v
    features := v.features },
  Spec.Siv.decryptApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.StackScratch.AArch64.withStackScratch 2576 .x7
      (Impl.AesSiv.AArch64.decrypt v.callee v.ctr.callee v.ctr.suffix)
    stack := 2576
    verified := decrypt_framed v
    features := v.features }]

end VG.Generic.CmacAesUpdate.AArch64.AesSiv
