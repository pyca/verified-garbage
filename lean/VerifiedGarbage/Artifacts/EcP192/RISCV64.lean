module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdh.P192.RISCV64
public import VerifiedGarbage.Proof.Ecdh.RISCV64.P192.PublicKeyVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.EcKey.P192
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Ecdh.RISCV64.P192.EcdhLit
public import VerifiedGarbage.Proof.P192.RISCV64.Law

/-! # P-192 public keys (FIPS 186-5 §A.2) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.EcP192.RISCV64

open VG.Proof.P192.RISCV64 (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.P192.publicKeyApi.artifact RISCV64.target {
    code := Impl.Ecdh.RISCV64.publicKeyP192
    verified := Proof.Ecdh.RISCV64.P192.pk_verified hasLaw.law }]

end VG.Artifacts.EcP192.RISCV64
