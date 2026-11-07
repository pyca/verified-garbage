module

public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Backend
public import VerifiedGarbage.Impl.RsaKeyGen.TrialTable32
public import VerifiedGarbage.Spec.RsaKeyGen.KeySearchContract
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Generate.Verified
public import VerifiedGarbage.Proof.Rsa.RISCV64.Instances
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # RSA key generation on RISC-V, its prime searches' candidates calling each shared Miller–Rabin implementation -/

@[expose] public section

namespace VG.Generic.MillerRabin.RISCV64.RsaKeyGen

def artifacts (v : Proof.MillerRabin.RISCV64.RoundImpl) : List Artifact := [
  Spec.RsaKeyGen.keySearchApi.artifact RISCV64.target {
    suffix := v.suffix
    stack := 656
    code := Proof.RsaKeyGen.RISCV64.Generate.genCode v
    verified := Proof.RsaKeyGen.RISCV64.Generate.gen_verified v
    features := v.features }]

end VG.Generic.MillerRabin.RISCV64.RsaKeyGen
