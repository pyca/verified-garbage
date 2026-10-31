module

public import VerifiedGarbage.Proof.AesOcb.Arm.Init
public import VerifiedGarbage.Proof.AesOcb.Arm.Frame
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# AES-OCB (RFC 7253) on ARMv7

A registration file (see `TCB/Emit.lean`): the artifacts it lists are emitted.
**Review note**: `sig` and `doc` are trusted, as they tie the Rust caller to
the contract; check them against the contract's `pre`/`post`. An artifact made
from a function's `Api` (in `Spec/`, reviewed with the contract) takes them
from there.

An AES-OCB key context is an AES-GCM one (the key schedule, then the
encrypted zero block at byte 240), so `init` is AES-GCM's code, in a frame of
2560 bytes holding its working space (`Proof/AesOcb/Arm/Init.lean`). `seal`
and `open` run in a frame of 2592 bytes holding theirs
(`Proof/AesOcb/Arm/Frame.lean`), and call `vg_aes_encrypt_blocks` and
`vg_aes_decrypt_blocks` in frames that push their stack argument and `lr`:
2600 bytes of stack in all.
-/

@[expose] public section

namespace VG.Artifacts.AesOcb.Arm

open VG.Proof.AesOcb.Arm

def artifacts : List Artifact := [
  Spec.Ocb.initApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withRegScratch 2560 .r3 Impl.AesGcm.Arm.init
    stack := 2568
    verified := init_framed },
  Spec.Ocb.sealApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch 2592 6 Impl.AesOcb.Arm.«seal»
    stack := 2600
    verified := seal_framed },
  Spec.Ocb.openApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch 2592 6 Impl.AesOcb.Arm.«open»
    stack := 2600
    verified := open_framed }]

end VG.Artifacts.AesOcb.Arm
