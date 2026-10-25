module

public import VerifiedGarbage.Proof.AesCfb8.RISCV64.Verified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.AesCfb8.RISCV64.Lit

/-!
# AES-CFB8 (NIST SP 800-38A §6.3) on RISC-V

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. RISC-V has one implementation of the block functions, so these are
not generic over them. A call (`jal`) stores nothing in memory, and the
return address is saved in the scratch buffer, so no stack is used.
-/

@[expose] public section

namespace VG.Artifacts.AesCfb8.RISCV64

open VG.Proof.AesCfb8.RISCV64

def artifacts : List Artifact := [
  Spec.Cfb8.aesEncryptApi.artifact RISCV64.target {
    notes := [
      "This implementation enciphers one block for each byte with `vg_aes_encrypt_blocks`. The \
        input block is copied and shifted a byte at a time, since the contract states no alignment \
        for it."]
    code := Impl.AesCfb8.RISCV64.encrypt
    verified := encrypt_verified },
  Spec.Cfb8.aesDecryptApi.artifact RISCV64.target {
    notes := [
      "This implementation enciphers one block for each byte with `vg_aes_encrypt_blocks`. The \
        input block is copied and shifted a byte at a time, since the contract states no alignment \
        for it."]
    code := Impl.AesCfb8.RISCV64.decrypt
    verified := decrypt_verified }]

end VG.Artifacts.AesCfb8.RISCV64
