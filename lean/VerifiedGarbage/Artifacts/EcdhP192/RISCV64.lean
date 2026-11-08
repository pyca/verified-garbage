module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdh.P192.RISCV64
public import VerifiedGarbage.Proof.Ecdh.RISCV64.P192.EcdhVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdh.P192
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Ecdh.RISCV64.P192.EcdhLit
public import VerifiedGarbage.Proof.P192.RISCV64.Law

/-! # ECDH over P-192 (SP 800-56A §5.7.1.2) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.EcdhP192.RISCV64

open VG.Proof.P192.RISCV64 (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdh.P192.exchangeApi.artifact RISCV64.target {
    code := Impl.Ecdh.RISCV64.ecdhP192
    verified := Proof.Ecdh.RISCV64.P192.ecdh_verified hasLaw.law }]

end VG.Artifacts.EcdhP192.RISCV64
