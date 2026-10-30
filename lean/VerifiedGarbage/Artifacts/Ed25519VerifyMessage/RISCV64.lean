module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.VerifyMsgVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Ed25519's verification of a message, on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Ed25519VerifyMessage.RISCV64

def artifacts : List Artifact := [
  Spec.Ed25519.verifyApi.artifact RISCV64.target {
    code := Impl.Ed25519.RISCV64.Whole.verifyCode
    stack := 480
    verified := Proof.Ed25519.RISCV64.Whole.verify_framed }]

end VG.Artifacts.Ed25519VerifyMessage.RISCV64
