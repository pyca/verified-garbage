module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ed25519.KeyPair
public import VerifiedGarbage.Spec.Ed25519.ExpandedSign
public import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Proof.Ed25519.RISCV64.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Ed25519 (RFC 8032) on RISC-V -/

namespace VG.Artifacts.Ed25519.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Ed25519.keyPairApi.artifact RISCV64.target {
    code := Impl.Ed25519.RISCV64.Fn.keyPair Proof.Ed25519.RISCV64.KeyPair.dgCode
    verified := Proof.Ed25519.RISCV64.Fn.keyPair },
  Spec.Ed25519.signExpandedApi.artifact RISCV64.target {
    code := Impl.Ed25519.RISCV64.Fn.signExpanded
    verified := Proof.Ed25519.RISCV64.Fn.signExpanded },
  Spec.Ed25519.verifyApi.artifact RISCV64.target {
    code := Impl.Ed25519.RISCV64.Fn.verify
    verified := Proof.Ed25519.RISCV64.Fn.verify }]

spec_apis artifacts

end VG.Artifacts.Ed25519.RISCV64
