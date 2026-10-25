module

public import VerifiedGarbage.Proof.AesCtr.RISCV64.Verified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.AesCtr.RISCV64.Lit

/-!
# AES-CTR (NIST SP 800-38A §6.5) on RISC-V

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. RISC-V has one implementation of `vg_aes_ctr32`, so this is not
generic over it. A call (`jal`) stores nothing in memory, and the return
address is saved in the scratch buffer, so no stack is used.
-/

@[expose] public section

namespace VG.Artifacts.AesCtr.RISCV64

def artifacts : List Artifact := [
  Spec.Ctr.aesApi.artifact RISCV64.target {
    notes := [
      "This implementation calls `vg_aes_ctr32` on as many blocks at once as the counter's \
        last 32 bits allow, as OpenSSL's `CRYPTO_ctr128_encrypt_ctr32` does. The counter block is \
        accessed a byte at a time, since the contract states no alignment for it."]
    code := Impl.AesCtr.RISCV64.crypt
    verified := Proof.AesCtr.RISCV64.crypt_verified }]

end VG.Artifacts.AesCtr.RISCV64
