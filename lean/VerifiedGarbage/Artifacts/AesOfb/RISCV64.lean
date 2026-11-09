module

public import VerifiedGarbage.Proof.AesOfb.RISCV64.Verified
public import VerifiedGarbage.Proof.AesOfb.RISCV64.Final
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # AES-OFB (NIST SP 800-38A §6.4) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.AesOfb.RISCV64

def artifacts : List Artifact := [
  Spec.Ofb.aesApi.artifact RISCV64.target {
    code := Impl.AesOfb.RISCV64.crypt
    verified := Proof.AesOfb.keyed Proof.AesOfb.RISCV64.crypt_verified },
  Spec.Ofb.aesFinalApi.artifact RISCV64.target {
    code := Impl.StackScratch.RISCV64.withStackScratchWiped 64 .a6 8 Impl.AesOfb.RISCV64.cryptFinal
    stack := 64
    verified := Proof.AesOfb.final_keyed Proof.AesOfb.RISCV64.cryptFinal_framed }]

end VG.Artifacts.AesOfb.RISCV64
