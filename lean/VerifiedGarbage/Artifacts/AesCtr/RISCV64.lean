module

public import VerifiedGarbage.Proof.AesCtr.RISCV64.Verified
public import VerifiedGarbage.Proof.AesCtr.RISCV64.Final
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.AesCtr.RISCV64.Lit

/-! # AES-CTR (NIST SP 800-38A §6.5) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.AesCtr.RISCV64

def artifacts : List Artifact := [
  Spec.Ctr.aesApi.artifact RISCV64.target {
    code := Impl.AesCtr.RISCV64.crypt
    verified := Proof.AesCtr.keyed Proof.AesCtr.RISCV64.crypt_verified },
  Spec.Ctr.aesFinalApi.artifact RISCV64.target {
    code := Impl.StackScratch.RISCV64.withStackScratchWiped 80 .a6 10 Impl.AesCtr.RISCV64.cryptFinal
    stack := 80
    verified := Proof.AesCtr.final_keyed Proof.AesCtr.RISCV64.Final.cryptFinal_framed }]

end VG.Artifacts.AesCtr.RISCV64
