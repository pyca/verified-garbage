module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdh.BrainpoolP384r1.RISCV64
public import VerifiedGarbage.Proof.Ecdh.RISCV64.BrainpoolP384r1.PublicKeyVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.EcKey.BrainpoolP384r1
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Ecdh.RISCV64.BrainpoolP384r1.EcdhLit
public import VerifiedGarbage.Proof.BrainpoolP384r1.RISCV64.Law

/-! # brainpoolP384r1 public keys (FIPS 186-5 §A.2) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.EcBrainpoolP384r1.RISCV64

open VG.Proof.BrainpoolP384r1.RISCV64 (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.BrainpoolP384r1.publicKeyApi.artifact RISCV64.target {
    code := Impl.Ecdh.RISCV64.publicKeyBrainpoolP384r1
    verified := Proof.Ecdh.RISCV64.BrainpoolP384r1.pk_verified hasLaw.law }]

end VG.Artifacts.EcBrainpoolP384r1.RISCV64
