module

public import VerifiedGarbage.Proof.AesGcm.Arm.Gather.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# AES-GCM (NIST SP 800-38D) on ARMv7

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.

Each function calls `vg_aes_ctr32` or `vg_ghash` in a frame that pushes
their two stack arguments, so uses 8 bytes of stack (`init` also calls
`vg_aes_expand_key_scratch`, which takes no stack arguments). Every function also
keeps its working space in a frame of its own (2560 bytes for `init`, 2576
for `stream_init` and `stream_aad`, 2592 for the others,
`Proof/AesGcm/Arm/Frame.lean`). `seal_gather` copies the slices to `dst` and
calls `vg_aes_gcm_seal` on them there, from a frame of 40 bytes
(`Proof/AesGcm/Arm/Gather/`).
-/

@[expose] public section

namespace VG.Artifacts.AesGcm.Arm

open VG.Proof.AesGcm.Arm

/-- How `init` is built. -/
def initNote : String := "This implementation calls `vg_aes_expand_key_scratch` for the key schedule and \
  `vg_aes_ctr32` to encrypt the zero block into the hash subkey."

/-- How `stream_init` and `stream_aad` are built. -/
def ghashNote : String := "This implementation calls `vg_ghash` for GHASH."

/-- How the other functions are built. -/
def callNote : String := "This implementation calls `vg_aes_ctr32` for the block cipher and `vg_ghash` for GHASH."

/-- How `seal_gather` is built. -/
def gatherNote : String :=
  "This implementation copies the slices, a word at a time, one after the other to `dst`, and \
    encrypts them there in place with `" ++ Spec.Gcm.sealApi.name ++ "`."

def artifacts : List Artifact := [
  Spec.Gcm.initApi.artifact Arm.target {
    notes := [initNote]
    code := Impl.StackScratch.Arm.withRegScratch 2560 .r3 Impl.AesGcm.Arm.init
    stack := 2568
    verified := init_framed },
  Spec.Gcm.sealApi.artifact Arm.target {
    notes := [callNote]
    code := Impl.StackScratch.Arm.withStackScratch 2592 5 Impl.AesGcm.Arm.«seal»
    stack := 2600
    verified := seal_framed },
  Spec.Gcm.openApi.artifact Arm.target {
    notes := [callNote]
    code := Impl.StackScratch.Arm.withStackScratch 2592 6 Impl.AesGcm.Arm.«open»
    stack := 2600
    verified := open_framed },
  Spec.Gcm.streamInitApi.artifact Arm.target {
    notes := [ghashNote]
    code := Impl.StackScratch.Arm.withStackScratch 2576 0 Impl.AesGcm.Arm.streamInit
    stack := 2584
    verified := streamInit_framed },
  Spec.Gcm.streamAadApi.artifact Arm.target {
    notes := [ghashNote]
    code := Impl.StackScratch.Arm.withStackScratch 2576 2 Impl.AesGcm.Arm.streamAad
    stack := 2584
    verified := streamAad_framed },
  Spec.Gcm.streamEncryptApi.artifact Arm.target {
    notes := [callNote]
    code := Impl.StackScratch.Arm.withStackScratch 2592 6 Impl.AesGcm.Arm.streamEncrypt
    stack := 2600
    verified := streamEncrypt_framed },
  Spec.Gcm.streamDecryptApi.artifact Arm.target {
    notes := [callNote]
    code := Impl.StackScratch.Arm.withStackScratch 2592 6 Impl.AesGcm.Arm.streamDecrypt
    stack := 2600
    verified := streamDecrypt_framed },
  Spec.Gcm.streamFinishApi.artifact Arm.target {
    notes := [callNote]
    code := Impl.StackScratch.Arm.withStackScratch 2592 5 Impl.AesGcm.Arm.streamFinish
    stack := 2600
    verified := streamFinish_framed },
  Spec.Gcm.streamVerifyApi.artifact Arm.target {
    notes := [callNote]
    code := Impl.StackScratch.Arm.withStackScratch 2592 6 Impl.AesGcm.Arm.streamVerify
    stack := 2600
    verified := streamVerify_framed },
  Spec.Gcm.sealGatherApi.artifact Arm.target {
    notes := [gatherNote]
    code := Impl.AesGcm.Arm.SealGather.sealGather Gather.sealFn.name Gather.sealFn.code
    stack := 2640
    verified := Gather.sealGather_verified Gather.sealFn }]

end VG.Artifacts.AesGcm.Arm
