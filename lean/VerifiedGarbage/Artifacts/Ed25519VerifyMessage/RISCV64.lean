module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.VerifyMsgVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Ed25519's verification of a message, on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Ed25519VerifyMessage.RISCV64

def artifacts : List Artifact := [
  Spec.Ed25519.verifyApi.artifact RISCV64.target {
    notes := ["Includes SHA-512 of R || A || message (calls of SHA-512's streaming functions), \
      challenge reduction (a call of `vg_ed25519_scalar_reduce`), and strict verification of the \
      Ed25519 equation (a call of `vg_ed25519_verify_equation`). The challenge, its digest, copies \
      of the signature and `pk`, the saved callee-saved registers and `ra` are in a frame of 272 \
      bytes on the stack."]
    code := Impl.Ed25519.RISCV64.Whole.verifyCode
    stack := 480
    verified := Proof.Ed25519.RISCV64.Whole.verify_framed }]

end VG.Artifacts.Ed25519VerifyMessage.RISCV64
