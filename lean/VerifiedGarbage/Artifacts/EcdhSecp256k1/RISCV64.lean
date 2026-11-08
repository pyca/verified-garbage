module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdh.Secp256k1.RISCV64
public import VerifiedGarbage.Proof.Ecdh.RISCV64.Secp256k1.EcdhVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdh.Secp256k1
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Ecdh.RISCV64.Secp256k1.EcdhLit
public import VerifiedGarbage.Proof.Secp256k1.RISCV64.Law

/-! # ECDH over secp256k1 (SP 800-56A §5.7.1.2) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.EcdhSecp256k1.RISCV64

open VG.Proof.Secp256k1.RISCV64 (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdh.Secp256k1.exchangeApi.artifact RISCV64.target {
    code := Impl.Ecdh.RISCV64.ecdhSecp256k1
    verified := Proof.Ecdh.RISCV64.Secp256k1.ecdh_verified hasLaw.law }]

end VG.Artifacts.EcdhSecp256k1.RISCV64
