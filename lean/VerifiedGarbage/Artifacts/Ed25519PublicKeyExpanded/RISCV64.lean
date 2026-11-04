module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.ExpandedVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Ed25519's public key from the seed's SHA-512 digest, on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Ed25519PublicKeyExpanded.RISCV64

def artifacts : List Artifact := [
  Spec.Ed25519.publicKeyExpandedApi.artifact RISCV64.target {
    consts := Impl.Ed25519.RISCV64.combConsts
    code := Impl.Ed25519.RISCV64.Whole.publicKeyExpandedCode
    stack := 352
    verified := Proof.Ed25519.RISCV64.Whole.publicKeyExpanded_framed }]

end VG.Artifacts.Ed25519PublicKeyExpanded.RISCV64
