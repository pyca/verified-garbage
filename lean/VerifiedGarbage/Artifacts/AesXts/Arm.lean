module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.AesXts.Arm.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# XTS-AES (IEEE Std 1619-2007, NIST SP 800-38E) on ARMv7

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. ARMv7 has one implementation of the block functions, so these are
not generic over them.

Each function calls `vg_aes_encrypt_blocks` or `vg_aes_decrypt_blocks` in a
frame that pushes its stack argument and `lr`, so uses 8 bytes of stack.
-/

@[expose] public section

namespace VG.Artifacts.AesXts.Arm

open VG.Proof.AesXts.Arm

def artifacts : List Artifact := [
  Spec.Xts.aesEncryptApi.artifact Arm.target {
    notes := [
      "This implementation enciphers one block at a time with `vg_aes_encrypt_blocks`."]
    code := Impl.AesXts.Arm.encrypt
    stack := 8
    verified := encrypt_verified },
  Spec.Xts.aesDecryptApi.artifact Arm.target {
    notes := [
      "This implementation deciphers one block at a time with `vg_aes_decrypt_blocks`."]
    code := Impl.AesXts.Arm.decrypt
    stack := 8
    verified := decrypt_verified }]

end VG.Artifacts.AesXts.Arm
