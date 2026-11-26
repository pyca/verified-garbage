module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ecdh.P224
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Impl.Ecdh.P224.RISCV64
import VerifiedGarbage.Proof.Ecdh.RISCV64.P224.EcdhVerified
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Ecdh.RISCV64.P224.EcdhLit
import VerifiedGarbage.Proof.P224.RISCV64.Law
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ECDH over P-224 (SP 800-56A) on RISC-V -/

namespace VG.Artifacts.EcdhP224.RISCV64

open VG.Proof.P224.RISCV64 (hasLaw)

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Ecdh.P224.exchangeApi.artifact RISCV64.target {
    code := Impl.Ecdh.RISCV64.Fn.exchangeP224
    verified := Proof.Ecdh.RISCV64.P224.exchange_scrubbed hasLaw.law }]

spec_apis artifacts

end VG.Artifacts.EcdhP224.RISCV64
