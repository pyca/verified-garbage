module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdh.P256.RISCV64
public import VerifiedGarbage.Proof.Ecdh.RISCV64.P256.EcdhVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdh.P256
import VerifiedGarbage.Proof.Ecdh.RISCV64.P256.EcdhLit

/-! # ECDH over P-256 (SP 800-56A §5.7.1.2) on RISC-V -/

@[expose] public section

namespace VG.Generic.P256.RISCV64.EcdhP256

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P256.curve) : List Artifact := [
  Spec.Ecdh.P256.exchangeApi.artifact RISCV64.target {
    code := Impl.Ecdh.RISCV64.ecdhP256
    verified := Proof.Ecdh.RISCV64.P256.ecdh_verified h.law }]

end VG.Generic.P256.RISCV64.EcdhP256
