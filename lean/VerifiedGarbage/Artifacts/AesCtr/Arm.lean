module

public import VerifiedGarbage.Proof.AesCtr.Arm.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# AES-CTR (NIST SP 800-38A §6.5) on ARMv7

A registration file (see `TCB/Emit.lean`): the artifact it lists is
emitted. ARMv7 has one implementation of the block functions, so it is not
generic over them.

The function calls `vg_aes_encrypt_blocks` in a frame that pushes its stack
argument and `lr`, so uses 8 bytes of stack.
-/

@[expose] public section

namespace VG.Artifacts.AesCtr.Arm

open VG.Proof.AesCtr.Arm

def artifacts : List Artifact := [
  Spec.Ctr.aesApi.artifact Arm.target {
    notes := [
      "This implementation enciphers one block at a time with `vg_aes_encrypt_blocks`."]
    code := Impl.AesCtr.Arm.crypt
    stack := 8
    verified := crypt_verified }]

end VG.Artifacts.AesCtr.Arm
