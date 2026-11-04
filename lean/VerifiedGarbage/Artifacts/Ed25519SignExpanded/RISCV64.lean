module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.ExpandedVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Ed25519's signature, from the seed's SHA-512 digest and the public key, on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Ed25519SignExpanded.RISCV64

def artifacts : List Artifact := [
  Spec.Ed25519.signExpandedApi.artifact RISCV64.target {
    consts := Impl.Ed25519.RISCV64.combConsts
    code := Impl.Ed25519.RISCV64.Whole.signExpandedCode
    stack := 496
    verified := Proof.Ed25519.RISCV64.Whole.signExpanded_framed }]

end VG.Artifacts.Ed25519SignExpanded.RISCV64
