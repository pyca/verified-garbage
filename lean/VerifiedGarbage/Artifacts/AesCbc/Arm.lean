import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.AesCbc.Arm.Verified

/-!
# AES-CBC (NIST SP 800-38A §6.2) on ARMv7

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. ARMv7 has one implementation of the block functions, so these are
not generic over them.

Each function calls `vg_aes_encrypt_blocks` or `vg_aes_decrypt_blocks` in a
frame that pushes its stack argument and `lr`, so uses 8 bytes of stack.
-/

namespace VG.Artifacts.AesCbc.Arm

open VG.Proof.AesCbc.Arm

def artifacts : List Artifact := [
  { Spec.Cbc.aesEncryptApi with
    target := Arm.target
    doc := Spec.Cbc.aesEncryptApi.doc (notes := [
      "This implementation enciphers one block at a time with `vg_aes_encrypt_blocks`."])
    code := Impl.AesCbc.Arm.encrypt
    contract := Spec.Cbc.aesEncryptContract Arm.abi 8
    stack := 8
    verified := encrypt_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Cbc.aesDecryptApi with
    target := Arm.target
    doc := Spec.Cbc.aesDecryptApi.doc (notes := [
      "This implementation deciphers one block at a time with `vg_aes_decrypt_blocks`."])
    code := Impl.AesCbc.Arm.decrypt
    contract := Spec.Cbc.aesDecryptContract Arm.abi 8
    stack := 8
    verified := decrypt_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.AesCbc.Arm
