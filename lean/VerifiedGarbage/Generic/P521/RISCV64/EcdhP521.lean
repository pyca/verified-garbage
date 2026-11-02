module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdh.P521.RISCV64
public import VerifiedGarbage.Proof.Ecdh.RISCV64.P521.EcdhVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdh.P521
import VerifiedGarbage.Proof.Ecdh.RISCV64.P521.EcdhLit

/-! # ECDH over P-521 (SP 800-56A §5.7.1.2) on RISC-V -/

@[expose] public section

namespace VG.Generic.P521.RISCV64.EcdhP521

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P521.curve) : List Artifact := [
  Spec.Ecdh.P521.exchangeApi.artifact RISCV64.target {
    code := Impl.Ecdh.RISCV64.ecdhP521
    verified := Proof.Ecdh.RISCV64.P521.ecdh_verified h.law }]

end VG.Generic.P521.RISCV64.EcdhP521
