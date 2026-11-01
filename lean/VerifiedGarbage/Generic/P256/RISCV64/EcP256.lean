module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdh.P256.RISCV64
public import VerifiedGarbage.Proof.Ecdh.RISCV64.P256.PublicKeyVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.EcKey.P256
import VerifiedGarbage.Proof.Ecdh.RISCV64.P256.EcdhLit

/-! # P-256 public keys (FIPS 186-5 §A.2) on RISC-V -/

@[expose] public section

namespace VG.Generic.P256.RISCV64.EcP256

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P256.curve) : List Artifact := [
  Spec.EcKey.P256.publicKeyApi.artifact RISCV64.target {
    code := Impl.Ecdh.RISCV64.publicKeyP256
    consts := Impl.Ecdsa.RISCV64.Comb.p256CombConsts
    verified := Proof.Ecdh.RISCV64.P256.pk_verified h.law }]

end VG.Generic.P256.RISCV64.EcP256
