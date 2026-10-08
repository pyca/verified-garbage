import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.AesCfb.Arm.Verified

/-!
# AES-CFB128 (NIST SP 800-38A §6.3) on ARMv7

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. ARMv7 has one implementation of the block functions, so these are
not generic over them.

Each function calls `vg_aes_encrypt_blocks` (both directions use the
forward cipher) in a frame that pushes its stack argument and `lr`, so uses
8 bytes of stack.
-/

namespace VG.Artifacts.AesCfb.Arm

open VG.Proof.AesCfb.Arm

def artifacts : List Artifact := [
  { Spec.Cfb.aesEncryptApi with
    target := Arm.target
    doc := Spec.Cfb.aesEncryptApi.doc (notes := [
      "This implementation enciphers one block at a time with `vg_aes_encrypt_blocks`."])
    code := Impl.AesCfb.Arm.encrypt
    contract := Spec.Cfb.aesEncryptContract Arm.abi 8
    stack := 8
    verified := encrypt_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Cfb.aesDecryptApi with
    target := Arm.target
    doc := Spec.Cfb.aesDecryptApi.doc (notes := [
      "This implementation enciphers one block at a time with `vg_aes_encrypt_blocks`."])
    code := Impl.AesCfb.Arm.decrypt
    contract := Spec.Cfb.aesDecryptContract Arm.abi 8
    stack := 8
    verified := decrypt_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.AesCfb.Arm
