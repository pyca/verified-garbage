module

public import VerifiedGarbage.Proof.AesOcb.Arm.Init
public import VerifiedGarbage.Proof.AesOcb.Arm.Frame
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# AES-OCB (RFC 7253) on ARMv7

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation.

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

/-- How `init` is built. -/
def initNote : String := "This implementation calls `vg_aes_expand_key_scratch` for the key schedule and \
  `vg_aes_ctr32` to encrypt the zero block into `L_*`."

def artifacts : List Artifact := [
  Spec.Ocb.initApi.artifact Arm.target {
    notes := [initNote]
    code := Impl.StackScratch.Arm.withRegScratch 2560 .r3 Impl.AesGcm.Arm.init
    stack := 2568
    verified := init_framed },
  Spec.Ocb.sealApi.artifact Arm.target {
    notes := ["This implementation enciphers with `vg_aes_encrypt_blocks`."]
    code := Impl.StackScratch.Arm.withStackScratch 2592 6 Impl.AesOcb.Arm.«seal»
    stack := 2600
    verified := seal_framed },
  Spec.Ocb.openApi.artifact Arm.target {
    notes := [
      "This implementation enciphers with `vg_aes_encrypt_blocks`, and deciphers with `vg_aes_decrypt_blocks`.",
      "It compares the tags and overwrites the data with zeros without a branch on the result."]
    code := Impl.StackScratch.Arm.withStackScratch 2592 6 Impl.AesOcb.Arm.«open»
    stack := 2600
    verified := open_framed }]

end VG.Artifacts.AesOcb.Arm
