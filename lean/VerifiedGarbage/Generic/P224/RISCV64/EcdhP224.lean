module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdh.P224.RISCV64
public import VerifiedGarbage.Proof.Ecdh.RISCV64.P224.EcdhVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdh.P224
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Ecdh.RISCV64.P224.EcdhLit

/-! # ECDH over P-224 (SP 800-56A §5.7.1.2) on RISC-V -/

@[expose] public section

namespace VG.Generic.P224.RISCV64.EcdhP224

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P224.curve) : List Artifact := [
  Spec.Ecdh.P224.exchangeApi.artifact RISCV64.target {
    code := Impl.Ecdh.RISCV64.ecdhP224
    verified := Proof.Ecdh.RISCV64.P224.ecdh_verified h.law }]

end VG.Generic.P224.RISCV64.EcdhP224
