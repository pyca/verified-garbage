module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.SignVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Ed25519's signature, with the public key given, on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Ed25519SignCached.RISCV64

def artifacts : List Artifact := [
  Spec.Ed25519.signCachedApi.artifact RISCV64.target {
    consts := Impl.Ed25519.RISCV64.combConsts
    code := Impl.Ed25519.RISCV64.Whole.signCachedCode
    stack := 496
    verified := Proof.Ed25519.RISCV64.Whole.signCached_framed }]

end VG.Artifacts.Ed25519SignCached.RISCV64
