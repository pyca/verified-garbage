module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ecdh.P384
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Impl.Ecdsa.P384.RISCV64Window
import VerifiedGarbage.Proof.Ecdh.RISCV64.P384.EcdhVerified
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Ecdh.RISCV64.P384.EcdhLit
import VerifiedGarbage.Proof.P384.RISCV64.Law
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ECDH over P-384 (SP 800-56A) on RISC-V -/

namespace VG.Artifacts.EcdhP384.RISCV64

open VG.Proof.P384.RISCV64 (hasLaw)

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Ecdh.P384.exchangeApi.artifact RISCV64.target {
    code := Impl.Ecdh.RISCV64.Fn.exchangeP384
    verified := Proof.Ecdh.RISCV64.P384.exchange_scrubbed hasLaw.law }]

spec_apis artifacts

end VG.Artifacts.EcdhP384.RISCV64
