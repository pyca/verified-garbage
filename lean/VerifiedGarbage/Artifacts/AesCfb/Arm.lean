module

public import VerifiedGarbage.Proof.AesCfb.Arm.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# AES-CFB128 (NIST SP 800-38A §6.3) on ARMv7

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. ARMv7 has one implementation of the block functions, so these are
not generic over them.

Each function calls `vg_aes_encrypt_blocks` (both directions use the
forward cipher) in a frame that pushes its stack argument and `lr`, so uses
8 bytes of stack.
-/

@[expose] public section

namespace VG.Artifacts.AesCfb.Arm

open VG.Proof.AesCfb.Arm

def artifacts : List Artifact := [
  Spec.Cfb.aesEncryptApi.artifact Arm.target {
    notes := [
      "This implementation enciphers one block at a time with `vg_aes_encrypt_blocks`."]
    code := Impl.AesCfb.Arm.encrypt
    stack := 8
    verified := encrypt_verified },
  Spec.Cfb.aesDecryptApi.artifact Arm.target {
    notes := [
      "This implementation enciphers one block at a time with `vg_aes_encrypt_blocks`."]
    code := Impl.AesCfb.Arm.decrypt
    stack := 8
    verified := decrypt_verified }]

end VG.Artifacts.AesCfb.Arm
