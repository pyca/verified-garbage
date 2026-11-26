module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ecdh.P256
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Impl.Ecdh.P256.RISCV64
import VerifiedGarbage.Proof.Ecdh.RISCV64.P256.EcdhVerified
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Ecdh.RISCV64.P256.EcdhLit
import VerifiedGarbage.Proof.P256.RISCV64.Law
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ECDH over P-256 (SP 800-56A) on RISC-V -/

namespace VG.Artifacts.EcdhP256.RISCV64

open VG.Proof.P256.RISCV64 (hasLaw)

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Ecdh.P256.exchangeApi.artifact RISCV64.target {
    code := Impl.Ecdh.RISCV64.Fn.exchangeP256
    verified := Proof.Ecdh.RISCV64.P256.exchange_scrubbed hasLaw.law }]

spec_apis artifacts

end VG.Artifacts.EcdhP256.RISCV64
