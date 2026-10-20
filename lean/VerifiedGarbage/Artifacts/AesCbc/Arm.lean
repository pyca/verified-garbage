module

public import VerifiedGarbage.Proof.AesCbc.Arm.Verified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.AesCbc.Arm.Body

/-!
# AES-CBC (NIST SP 800-38A §6.2) on ARMv7

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. ARMv7 has one implementation of the block functions, so these are
not generic over them.

Each function calls `vg_aes_encrypt_blocks` or `vg_aes_decrypt_blocks` in a
frame that pushes its stack argument and `lr`, so uses 8 bytes of stack.
-/

@[expose] public section

namespace VG.Artifacts.AesCbc.Arm

open VG.Proof.AesCbc.Arm

def artifacts : List Artifact := [
  Spec.Cbc.aesEncryptApi.artifact Arm.target {
    notes := [
      "This implementation enciphers one block at a time with `vg_aes_encrypt_blocks`."]
    code := Impl.AesCbc.Arm.encrypt
    stack := 8
    verified := encrypt_verified },
  Spec.Cbc.aesDecryptApi.artifact Arm.target {
    notes := [
      "This implementation deciphers one block at a time with `vg_aes_decrypt_blocks`."]
    code := Impl.AesCbc.Arm.decrypt
    stack := 8
    verified := decrypt_verified }]

end VG.Artifacts.AesCbc.Arm
