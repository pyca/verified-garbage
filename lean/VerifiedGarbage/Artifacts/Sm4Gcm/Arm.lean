module

public import VerifiedGarbage.Proof.Sm4.Arm.Batch32Verified
public import VerifiedGarbage.Proof.Sm4Gcm.Arm.Frame
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# SM4-GCM on baseline ARMv7

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. Each artifact is made from its function's `Api` (in `Spec/`, reviewed
with the contract), and this file adds only notes on the implementation.

The AEAD functions are AES-GCM's code with SM4 in place of AES: they call
`vg_sm4_ctr32` for the block cipher (in a frame of 1520 bytes, the most stack
any of their calls uses) and `vg_ghash` for GHASH, and `init` calls
`vg_sm4_expand_key` for the key schedule. Every function also keeps its
768-byte working space in a frame of its own (768 bytes for `init`, 784 for
`stream_init` and `stream_aad`, 800 for the others,
`Proof/Sm4Gcm/Arm/Frame.lean`).
-/

@[expose] public section

namespace VG.Artifacts.Sm4Gcm.Arm

open VG.Proof.Sm4Gcm.Arm

/-- How `init` is built. -/
def initNote : String := "Baseline ARMv7: calls `vg_sm4_expand_key` for the key schedule and \
  `vg_sm4_ctr32` to encrypt the zero block into the hash subkey."

/-- How `stream_init` and `stream_aad` are built. -/
def ghashNote : String := "Baseline ARMv7: calls `vg_ghash` for GHASH."

/-- How the other functions are built. -/
def callNote : String :=
  "Baseline ARMv7: calls `vg_sm4_ctr32` for the block cipher and `vg_ghash` for GHASH."

def artifacts : List Artifact := [
  Spec.Sm4.ctr32Api.artifact Arm.target {
    notes := ["Baseline ARMv7: `vg_sm4_ctr`'s code (the bitsliced round-key table prepared once per message, then up to eight independent counters encrypted per batch) with GCM's `inc₃₂` on the counter: only its last word, byte-reversed, incremented and stored back. The 1512-byte working space is kept on the stack and zeroed on return."]
    code := Impl.Sm4.Arm.BatchCtr32.ctr32Framed
    stack := 1520
    verified := Proof.Sm4.Arm.Batch32Verified.framed },
  Spec.Sm4.Gcm.initApi.artifact Arm.target {
    notes := [initNote]
    code := Impl.StackScratch.Arm.withRegScratch 768 .r2 Impl.Sm4Gcm.Arm.init
    stack := 2288
    verified := init_framed },
  Spec.Sm4.Gcm.sealApi.artifact Arm.target {
    notes := [callNote]
    code := Impl.StackScratch.Arm.withStackScratch 800 4 Impl.Sm4Gcm.Arm.«seal»
    stack := 2320
    verified := seal_framed },
  Spec.Sm4.Gcm.openApi.artifact Arm.target {
    notes := [callNote]
    code := Impl.StackScratch.Arm.withStackScratch 800 5 Impl.Sm4Gcm.Arm.«open»
    stack := 2320
    verified := open_framed },
  Spec.Sm4.Gcm.streamInitApi.artifact Arm.target {
    notes := [ghashNote]
    code := Impl.StackScratch.Arm.withStackScratch 784 0 Impl.Sm4Gcm.Arm.streamInit
    stack := 2304
    verified := streamInit_framed },
  Spec.Sm4.Gcm.streamAadApi.artifact Arm.target {
    notes := [ghashNote]
    code := Impl.StackScratch.Arm.withStackScratch 784 2 Impl.Sm4Gcm.Arm.streamAad
    stack := 2304
    verified := streamAad_framed },
  Spec.Sm4.Gcm.streamEncryptApi.artifact Arm.target {
    notes := [callNote]
    code := Impl.StackScratch.Arm.withStackScratch 800 4 Impl.Sm4Gcm.Arm.streamEncrypt
    stack := 2320
    verified := streamEncrypt_framed },
  Spec.Sm4.Gcm.streamDecryptApi.artifact Arm.target {
    notes := [callNote]
    code := Impl.StackScratch.Arm.withStackScratch 800 4 Impl.Sm4Gcm.Arm.streamDecrypt
    stack := 2320
    verified := streamDecrypt_framed },
  Spec.Sm4.Gcm.streamFinishApi.artifact Arm.target {
    notes := [callNote]
    code := Impl.StackScratch.Arm.withStackScratch 800 3 Impl.Sm4Gcm.Arm.streamFinish
    stack := 2320
    verified := streamFinish_framed },
  Spec.Sm4.Gcm.streamVerifyApi.artifact Arm.target {
    notes := [callNote]
    code := Impl.StackScratch.Arm.withStackScratch 800 4 Impl.Sm4Gcm.Arm.streamVerify
    stack := 2320
    verified := streamVerify_framed }]

end VG.Artifacts.Sm4Gcm.Arm
