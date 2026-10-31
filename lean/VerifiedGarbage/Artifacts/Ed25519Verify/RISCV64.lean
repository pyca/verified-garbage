module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Ed25519.RISCV64.VerifyVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Ed25519's verification equation, on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Ed25519Verify.RISCV64

def artifacts : List Artifact := [
  Spec.Ed25519.verifyEquationApi.artifact RISCV64.target {
    code := Impl.Ed25519.RISCV64.verifyEquation
    verified := Proof.Ed25519.RISCV64.verifyEquation_verified }]

end VG.Artifacts.Ed25519Verify.RISCV64
