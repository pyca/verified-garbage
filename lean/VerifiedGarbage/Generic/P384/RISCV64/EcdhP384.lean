module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdh.P384.RISCV64
public import VerifiedGarbage.Proof.Ecdh.RISCV64.P384.EcdhVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdh.P384
import VerifiedGarbage.Proof.Ecdh.RISCV64.P384.EcdhLit

/-! # ECDH over P-384 (SP 800-56A §5.7.1.2) on RISC-V -/

@[expose] public section

namespace VG.Generic.P384.RISCV64.EcdhP384

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P384.curve) : List Artifact := [
  Spec.Ecdh.P384.exchangeApi.artifact RISCV64.target {
    code := Impl.Ecdh.RISCV64.ecdhP384
    verified := Proof.Ecdh.RISCV64.P384.ecdh_verified h.law }]

end VG.Generic.P384.RISCV64.EcdhP384
