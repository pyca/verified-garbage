module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ecdh.P192
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Impl.Ecdh.P192.RISCV64
import VerifiedGarbage.Proof.Ecdh.RISCV64.P192.EcdhVerified
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Ecdh.RISCV64.P192.EcdhLit
import VerifiedGarbage.Proof.P192.RISCV64.Law
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ECDH over P-192 (SP 800-56A) on RISC-V -/

namespace VG.Artifacts.EcdhP192.RISCV64

open VG.Proof.P192.RISCV64 (hasLaw)

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Ecdh.P192.exchangeApi.artifact RISCV64.target {
    code := Impl.Ecdh.RISCV64.Fn.exchangeP192
    verified := Proof.Ecdh.RISCV64.P192.exchange_scrubbed hasLaw.law }]

spec_apis artifacts

end VG.Artifacts.EcdhP192.RISCV64
