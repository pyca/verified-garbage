import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.AesCfb8.Arm.Verified

/-!
# AES-CFB8 (NIST SP 800-38A §6.3, with 8-bit segments) on ARMv7

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. ARMv7 has one implementation of the block functions, so these are
not generic over them.

Each function calls `vg_aes_encrypt_blocks` (both directions use the
forward cipher) in a frame that pushes its stack argument and `lr`, so uses
8 bytes of stack.
-/

namespace VG.Artifacts.AesCfb8.Arm

open VG.Proof.AesCfb8.Arm

def artifacts : List Artifact := [
  { Spec.Cfb8.aesEncryptApi with
    target := Arm.target
    doc := Spec.Cfb8.aesEncryptApi.doc (notes := [
      "This implementation enciphers one block for each byte with `vg_aes_encrypt_blocks`."])
    code := Impl.AesCfb8.Arm.encrypt
    contract := Spec.Cfb8.aesEncryptContract Arm.abi 8
    stack := 8
    verified := encrypt_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Cfb8.aesDecryptApi with
    target := Arm.target
    doc := Spec.Cfb8.aesDecryptApi.doc (notes := [
      "This implementation enciphers one block for each byte with `vg_aes_encrypt_blocks`."])
    code := Impl.AesCfb8.Arm.decrypt
    contract := Spec.Cfb8.aesDecryptContract Arm.abi 8
    stack := 8
    verified := decrypt_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.AesCfb8.Arm
