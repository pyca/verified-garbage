module

public import VerifiedGarbage.Proof.AesOfb.RISCV64.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# AES-OFB (NIST SP 800-38A §6.4) on RISC-V

A registration file (see `TCB/Emit.lean`): the artifact it lists is
emitted. RISC-V has one implementation of the block functions, so this is
not generic over them. A call (`jal`) stores nothing in memory, and the
return address is saved in the scratch buffer, so no stack is used.
-/

@[expose] public section

namespace VG.Artifacts.AesOfb.RISCV64

def artifacts : List Artifact := [
  Spec.Ofb.aesApi.artifact RISCV64.target {
    code := Impl.AesOfb.RISCV64.crypt
    verified := Proof.AesOfb.RISCV64.crypt_verified }]

end VG.Artifacts.AesOfb.RISCV64
