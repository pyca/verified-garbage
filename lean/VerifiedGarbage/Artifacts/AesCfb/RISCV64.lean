module

public import VerifiedGarbage.Proof.AesCfb.RISCV64.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# AES-CFB128 (NIST SP 800-38A §6.3) on RISC-V

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. RISC-V has one implementation of the block functions, so these are
not generic over them. A call (`jal`) stores nothing in memory, and the
return address is saved in the scratch buffer, so no stack is used.
-/

@[expose] public section

namespace VG.Artifacts.AesCfb.RISCV64

open VG.Proof.AesCfb.RISCV64

def artifacts : List Artifact := [
  Spec.Cfb.aesEncryptApi.artifact RISCV64.target {
    code := Impl.AesCfb.RISCV64.encrypt
    verified := encrypt_verified },
  Spec.Cfb.aesDecryptApi.artifact RISCV64.target {
    code := Impl.AesCfb.RISCV64.decrypt
    verified := decrypt_verified }]

end VG.Artifacts.AesCfb.RISCV64
