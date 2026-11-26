module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ecdh.Secp256k1
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Impl.Ecdh.Secp256k1.RISCV64
import VerifiedGarbage.Proof.Ecdh.RISCV64.Secp256k1.EcdhVerified
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Ecdh.RISCV64.Secp256k1.EcdhLit
import VerifiedGarbage.Proof.Secp256k1.RISCV64.Law
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ECDH over secp256k1 (SP 800-56A) on RISC-V -/

namespace VG.Artifacts.EcdhSecp256k1.RISCV64

open VG.Proof.Secp256k1.RISCV64 (hasLaw)

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Ecdh.Secp256k1.exchangeApi.artifact RISCV64.target {
    code := Impl.Ecdh.RISCV64.Fn.exchangeSecp256k1
    verified := Proof.Ecdh.RISCV64.Secp256k1.exchange_scrubbed hasLaw.law }]

spec_apis artifacts

end VG.Artifacts.EcdhSecp256k1.RISCV64
