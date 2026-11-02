module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdh.Secp256k1.RISCV64
public import VerifiedGarbage.Proof.Ecdh.RISCV64.Secp256k1.PublicKeyVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.EcKey.Secp256k1
import VerifiedGarbage.Proof.Ecdh.RISCV64.Secp256k1.EcdhLit

/-! # secp256k1 public keys (FIPS 186-5 §A.2) on RISC-V -/

@[expose] public section

namespace VG.Generic.Secp256k1.RISCV64.EcSecp256k1

def artifacts (h : Proof.Weierstrass.HasLaw Spec.Secp256k1.curve) : List Artifact := [
  Spec.EcKey.Secp256k1.publicKeyApi.artifact RISCV64.target {
    code := Impl.Ecdh.RISCV64.publicKeySecp256k1
    verified := Proof.Ecdh.RISCV64.Secp256k1.pk_verified h.law }]

end VG.Generic.Secp256k1.RISCV64.EcSecp256k1
