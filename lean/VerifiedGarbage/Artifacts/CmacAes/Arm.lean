module

public import VerifiedGarbage.Proof.CmacAes.Stream.Arm.Frame
public import VerifiedGarbage.Proof.CmacAes.Arm.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# AES-CMAC (NIST SP 800-38B) on ARMv7

Each function calls `vg_aes_ctr32` in a frame that pushes its two stack
arguments, so uses 8 bytes of stack. The streaming functions call those:
`init` calls `vg_cmac_aes_subkeys` (and `vg_aes_expand_key_scratch`, which uses no
stack), so uses 8 bytes; `absorb` and `finish` call `vg_cmac_aes_update`
and `vg_cmac_aes_finalize` in a frame that pushes their two stack arguments,
so use 16.

The streaming functions keep their working space in a frame of their own
on the stack (`Proof/CmacAes/Stream/Arm/Frame.lean`): their `stack` is that
frame and the stack their code uses below it.
-/

@[expose] public section

namespace VG.Artifacts.CmacAes.Arm

open VG.Proof.CmacAes.Arm

def artifacts : List Artifact := [
  Spec.Cmac.aesSubkeysApi.artifact Arm.target {
    code := Impl.CmacAes.Arm.subkeys
    stack := 8
    verified := subkeys_verified },
  Spec.Cmac.aesUpdateApi.artifact Arm.target {
    code := Impl.CmacAes.Arm.update
    stack := 8
    verified := update_verified },
  Spec.Cmac.aesFinalizeApi.artifact Arm.target {
    code := Impl.CmacAes.Arm.finalize
    stack := 8
    verified := finalize_verified },
  Spec.Cmac.aesInitApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withRegScratch 2304 .r3 Impl.CmacAes.Stream.Arm.init
    stack := 2312
    verified := Proof.CmacAes.Stream.Arm.init_framed },
  Spec.Cmac.aesAbsorbApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch 2320 2 Impl.CmacAes.Stream.Arm.absorb
    stack := 2336
    verified := Proof.CmacAes.Stream.Arm.absorb_framed },
  Spec.Cmac.aesFinishApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch 2320 1 Impl.CmacAes.Stream.Arm.finish
    stack := 2336
    verified := Proof.CmacAes.Stream.Arm.finish_framed }]

end VG.Artifacts.CmacAes.Arm
