module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.PublicKeyVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Ed25519's public key from a seed, on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Ed25519PublicKey.RISCV64

def artifacts : List Artifact := [
  Spec.Ed25519.publicKeyApi.artifact RISCV64.target {
    consts := Impl.Ed25519.RISCV64.combConsts
    code := Impl.Ed25519.RISCV64.Whole.publicKeyCode
    stack := 352
    verified := Proof.Ed25519.RISCV64.Whole.publicKey_framed }]

end VG.Artifacts.Ed25519PublicKey.RISCV64
