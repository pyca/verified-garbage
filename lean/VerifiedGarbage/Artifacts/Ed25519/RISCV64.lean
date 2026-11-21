module

public import VerifiedGarbage.Proof.Ed25519.RISCV64.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
public import VerifiedGarbage.TCB.RISCV64.Target

/-! # Ed25519 (RFC 8032) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Ed25519.RISCV64

def artifacts : List Artifact := [
  Spec.Ed25519.keyPairApi.artifact RISCV64.target {
    code := Impl.Ed25519.RISCV64.Fn.keyPair Proof.Ed25519.RISCV64.KeyPair.dgCode
    verified := Proof.Ed25519.RISCV64.Fn.keyPair },
  Spec.Ed25519.signExpandedApi.artifact RISCV64.target {
    code := Impl.Ed25519.RISCV64.Fn.signExpanded
    verified := Proof.Ed25519.RISCV64.Fn.signExpanded },
  Spec.Ed25519.verifyApi.artifact RISCV64.target {
    code := Impl.Ed25519.RISCV64.Fn.verify
    verified := Proof.Ed25519.RISCV64.Fn.verify }]

end VG.Artifacts.Ed25519.RISCV64
