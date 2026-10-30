module

public import VerifiedGarbage.Proof.Sm4.Arm.Batch32Verified
public import VerifiedGarbage.Proof.Sm4Gcm.Arm.Frame
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# SM4-GCM on baseline ARMv7

A registration file (see `TCB/Emit.lean`): the artifacts it lists are emitted.
Each artifact is made from its function's `Api` (in `Spec/`, reviewed with the
contract).

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

def artifacts : List Artifact := [
  Spec.Sm4.ctr32Api.artifact Arm.target {
    code := Impl.Sm4.Arm.BatchCtr32.ctr32Framed
    stack := 1520
    verified := Proof.Sm4.Arm.Batch32Verified.framed },
  Spec.Sm4.Gcm.initApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withRegScratch 768 .r2 Impl.Sm4Gcm.Arm.init
    stack := 2288
    verified := init_framed },
  Spec.Sm4.Gcm.sealApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch 800 4 Impl.Sm4Gcm.Arm.«seal»
    stack := 2320
    verified := seal_framed },
  Spec.Sm4.Gcm.openApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch 800 5 Impl.Sm4Gcm.Arm.«open»
    stack := 2320
    verified := open_framed },
  Spec.Sm4.Gcm.streamInitApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch 784 0 Impl.Sm4Gcm.Arm.streamInit
    stack := 2304
    verified := streamInit_framed },
  Spec.Sm4.Gcm.streamAadApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch 784 2 Impl.Sm4Gcm.Arm.streamAad
    stack := 2304
    verified := streamAad_framed },
  Spec.Sm4.Gcm.streamEncryptApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch 800 4 Impl.Sm4Gcm.Arm.streamEncrypt
    stack := 2320
    verified := streamEncrypt_framed },
  Spec.Sm4.Gcm.streamDecryptApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch 800 4 Impl.Sm4Gcm.Arm.streamDecrypt
    stack := 2320
    verified := streamDecrypt_framed },
  Spec.Sm4.Gcm.streamFinishApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch 800 3 Impl.Sm4Gcm.Arm.streamFinish
    stack := 2320
    verified := streamFinish_framed },
  Spec.Sm4.Gcm.streamVerifyApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch 800 4 Impl.Sm4Gcm.Arm.streamVerify
    stack := 2320
    verified := streamVerify_framed }]

end VG.Artifacts.Sm4Gcm.Arm
