module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdh.BrainpoolP384r1.RISCV64
public import VerifiedGarbage.Proof.Ecdh.RISCV64.BrainpoolP384r1.PublicKeyVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.EcKey.BrainpoolP384r1
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Ecdh.RISCV64.BrainpoolP384r1.EcdhLit

/-! # brainpoolP384r1 public keys (FIPS 186-5 §A.2) on RISC-V -/

@[expose] public section

namespace VG.Generic.BrainpoolP384r1.RISCV64.EcBrainpoolP384r1

def artifacts (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP384r1.curve) : List Artifact := [
  Spec.EcKey.BrainpoolP384r1.publicKeyApi.artifact RISCV64.target {
    code := Impl.Ecdh.RISCV64.publicKeyBrainpoolP384r1
    verified := Proof.Ecdh.RISCV64.BrainpoolP384r1.pk_verified h.law }]

end VG.Generic.BrainpoolP384r1.RISCV64.EcBrainpoolP384r1
