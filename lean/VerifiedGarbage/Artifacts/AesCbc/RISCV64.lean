module

public import VerifiedGarbage.Proof.AesCbc.RISCV64.Verified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.AesCbc.RISCV64.Lit

/-!
# AES-CBC (NIST SP 800-38A §6.2) on RISC-V

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. RISC-V has one implementation of the block functions, so these are
not generic over them. A call (`jal`) stores nothing in memory, and the
return address is saved in the scratch buffer, so no stack is used.
-/

@[expose] public section

namespace VG.Artifacts.AesCbc.RISCV64

open VG.Proof.AesCbc.RISCV64

def artifacts : List Artifact := [
  Spec.Cbc.aesEncryptApi.artifact RISCV64.target {
    code := Impl.AesCbc.RISCV64.encrypt
    verified := encrypt_verified },
  Spec.Cbc.aesDecryptApi.artifact RISCV64.target {
    code := Impl.AesCbc.RISCV64.decrypt
    verified := decrypt_verified }]

end VG.Artifacts.AesCbc.RISCV64
