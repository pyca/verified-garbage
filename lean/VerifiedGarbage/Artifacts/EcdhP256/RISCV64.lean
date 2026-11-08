module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdh.P256.RISCV64
public import VerifiedGarbage.Proof.Ecdh.RISCV64.P256.EcdhVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdh.P256
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Ecdh.RISCV64.P256.EcdhLit
public import VerifiedGarbage.Proof.P256.RISCV64.Law

/-! # ECDH over P-256 (SP 800-56A §5.7.1.2) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.EcdhP256.RISCV64

open VG.Proof.P256.RISCV64 (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdh.P256.exchangeApi.artifact RISCV64.target {
    code := Impl.Ecdh.RISCV64.ecdhP256
    verified := Proof.Ecdh.RISCV64.P256.ecdh_verified hasLaw.law }]

end VG.Artifacts.EcdhP256.RISCV64
