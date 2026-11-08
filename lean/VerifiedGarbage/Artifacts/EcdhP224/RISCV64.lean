module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdh.P224.RISCV64
public import VerifiedGarbage.Proof.Ecdh.RISCV64.P224.EcdhVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdh.P224
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Ecdh.RISCV64.P224.EcdhLit
public import VerifiedGarbage.Proof.P224.RISCV64.Law

/-! # ECDH over P-224 (SP 800-56A §5.7.1.2) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.EcdhP224.RISCV64

open VG.Proof.P224.RISCV64 (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdh.P224.exchangeApi.artifact RISCV64.target {
    code := Impl.Ecdh.RISCV64.ecdhP224
    verified := Proof.Ecdh.RISCV64.P224.ecdh_verified hasLaw.law }]

end VG.Artifacts.EcdhP224.RISCV64
