import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.AesXts.Arm.Verified

/-!
# XTS-AES (IEEE Std 1619-2007, NIST SP 800-38E) on ARMv7

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. ARMv7 has one implementation of the block functions, so these are
not generic over them.

Each function calls `vg_aes_encrypt_blocks` or `vg_aes_decrypt_blocks` in a
frame that pushes its stack argument and `lr`, so uses 8 bytes of stack.
-/

namespace VG.Artifacts.AesXts.Arm

open VG.Proof.AesXts.Arm

def artifacts : List Artifact := [
  { Spec.Xts.aesEncryptApi with
    target := Arm.target
    doc := Spec.Xts.aesEncryptApi.doc (notes := [
      "This implementation enciphers one block at a time with `vg_aes_encrypt_blocks`."])
    code := Impl.AesXts.Arm.encrypt
    contract := Spec.Xts.aesEncryptContract Arm.abi 8
    stack := 8
    verified := encrypt_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Xts.aesDecryptApi with
    target := Arm.target
    doc := Spec.Xts.aesDecryptApi.doc (notes := [
      "This implementation deciphers one block at a time with `vg_aes_decrypt_blocks`."])
    code := Impl.AesXts.Arm.decrypt
    contract := Spec.Xts.aesDecryptContract Arm.abi 8
    stack := 8
    verified := decrypt_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.AesXts.Arm
