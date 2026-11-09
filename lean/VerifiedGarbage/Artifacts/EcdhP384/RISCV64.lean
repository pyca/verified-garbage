module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdsa.P384.RISCV64Window
public import VerifiedGarbage.Proof.Ecdh.RISCV64.P384.EcdhVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdh.P384
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Ecdh.RISCV64.P384.EcdhLit
public import VerifiedGarbage.Proof.P384.RISCV64.Law

/-! # ECDH over P-384 (SP 800-56A §5.7.1.2) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.EcdhP384.RISCV64

open VG.Proof.P384.RISCV64 (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdh.P384.exchangeApi.artifact RISCV64.target {
    code := Impl.Ecdh.RISCV64.ecdhP384
    verified := Proof.Ecdh.RISCV64.P384.ecdh_verified hasLaw.law }]

end VG.Artifacts.EcdhP384.RISCV64
