module

public import VerifiedGarbage.Proof.AesCcm.Arm.Frame
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# AES-CCM (NIST SP 800-38C) on ARMv7

A registration file (see `TCB/Emit.lean`): the artifacts it lists are emitted.
**Review note**: `sig` and `doc` are trusted, as they tie the Rust caller to
the contract; check them against the contract's `pre`/`post`. An artifact made
from a function's `Api` (in `Spec/`, reviewed with the contract) takes them
from there.

Both functions run in a frame of 2592 bytes holding their working space
(`Proof/AesCcm/Arm/Frame.lean`). In it they call `vg_cmac_aes_update` and
`vg_aes_ctr32` in frames that push their two stack arguments, and
`vg_cmac_aes_update`'s own frame for its call of `vg_aes_ctr32` pushes two
more: 2608 bytes of stack in all.
-/

@[expose] public section

namespace VG.Artifacts.AesCcm.Arm

open VG.Proof.AesCcm.Arm

def artifacts : List Artifact := [
  Spec.Ccm.sealApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch 2592 6 Impl.AesCcm.Arm.«seal»
    stack := 2608
    verified := seal_framed },
  Spec.Ccm.openApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch 2592 6 Impl.AesCcm.Arm.«open»
    stack := 2608
    verified := open_framed }]

end VG.Artifacts.AesCcm.Arm
