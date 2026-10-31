module

public import VerifiedGarbage.Proof.CmacAes.Stream.AArch64.Frame
public import VerifiedGarbage.Proof.Framework.Registration
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
public import VerifiedGarbage.Proof.Gcm.Spec
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
import VerifiedGarbage.Proof.Gcm.Spec

/-!
# AES-CMAC (NIST SP 800-38B) on AArch64

A generic file (see `TCB/Emit.lean`): the artifacts it lists, calling an
implementation `v` of `vg_aes_ctr32`, are emitted once for each implementation
(`Variants/AesCtr32/AArch64/`), named with its suffix (e.g.
`vg_cmac_aes_update_aes`), and need its CPU features.

The functions use no stack: their calls (`bl`) keep the return address in
`x30`, which they save in the scratch buffer. The streaming functions
(`init`, `absorb`, `finish`) call the first three; `init` also calls the
implementation of `vg_aes_expand_key_scratch` that goes with `v`.

The streaming functions keep their working space in a frame of their own
on the stack (`Proof/CmacAes/Stream/AArch64/Frame.lean`): their `stack` is that
frame and the stack their code uses below it.
-/

@[expose] public section

namespace VG.Generic.AesCtr32.AArch64.CmacAes

open VG.Proof.CmacAes.AArch64

def artifacts (v : Proof.Aes.AArch64.Ctr32Impl) : List Artifact := [
  Spec.Cmac.aesSubkeysApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.CmacAes.AArch64.subkeys v.callee
    verified := subkeys_verified v
    features := v.features },
  Spec.Cmac.aesUpdateApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.CmacAes.AArch64.update v.callee
    verified := update_verified v
    features := v.features },
  Spec.Cmac.aesFinalizeApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.CmacAes.AArch64.finalize v.callee
    verified := finalize_verified v
    features := v.features },
  Spec.Cmac.aesInitApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.StackScratch.AArch64.withStackScratch 2304 .x3
      (Impl.CmacAes.Stream.AArch64.init v.expand v.callee v.suffix)
    stack := 2304
    verified := Proof.CmacAes.Stream.AArch64.init_framed v
    features := v.features },
  Spec.Cmac.aesFinishApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.StackScratch.AArch64.withStackScratch 2304 .x4
      (Impl.CmacAes.Stream.AArch64.finish v.callee v.suffix)
    stack := 2304
    verified := Proof.CmacAes.Stream.AArch64.finish_framed v
    features := v.features }]

end VG.Generic.AesCtr32.AArch64.CmacAes
