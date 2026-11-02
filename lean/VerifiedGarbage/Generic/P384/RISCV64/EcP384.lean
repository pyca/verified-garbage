module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdh.P384.RISCV64
public import VerifiedGarbage.Proof.Ecdh.RISCV64.P384.PublicKeyVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.EcKey.P384
import VerifiedGarbage.Proof.Ecdh.RISCV64.P384.EcdhLit

/-! # P-384 public keys (FIPS 186-5 §A.2) on RISC-V -/

@[expose] public section

namespace VG.Generic.P384.RISCV64.EcP384

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P384.curve) : List Artifact := [
  Spec.EcKey.P384.publicKeyApi.artifact RISCV64.target {
    code := Impl.Ecdh.RISCV64.publicKeyP384
    verified := Proof.Ecdh.RISCV64.P384.pk_verified h.law }]

end VG.Generic.P384.RISCV64.EcP384
