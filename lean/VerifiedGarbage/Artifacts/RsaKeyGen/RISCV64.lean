module

public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.KeyInit
public import VerifiedGarbage.Spec.RsaKeyGen.KeySearchContract
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Backend
public import VerifiedGarbage.Impl.RsaKeyGen.TrialTable32
public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Generate.Verified
public import VerifiedGarbage.Proof.Rsa.RISCV64.Instances
public import VerifiedGarbage.Proof.Variants.MillerRabin.RISCV64

/-! # RSA key generation (FIPS 186-5 A.1.3) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.RsaKeyGen.RISCV64

def direct : List Artifact := [
  Spec.RsaKeyGen.keyInitApi.artifact RISCV64.target {
    code := Impl.RsaKeyGen.RISCV64.KeyInit.init
    verified := Proof.RsaKeyGen.RISCV64.KeyInit.init_verified }]

end VG.Artifacts.RsaKeyGen.RISCV64

-- RSA key generation on RISC-V, its prime searches' candidates calling each shared Miller–Rabin implementation
namespace VG.Artifacts.RsaKeyGen.RISCV64.MillerRabin

def artifacts (v : Proof.MillerRabin.RISCV64.RoundImpl) : List Artifact := [
  Spec.RsaKeyGen.keySearchApi.artifact RISCV64.target {
    suffix := v.suffix
    stack := 656
    code := Proof.RsaKeyGen.RISCV64.Generate.genCode v
    verified := Proof.RsaKeyGen.RISCV64.Generate.gen_verified v
    features := v.features }]

end VG.Artifacts.RsaKeyGen.RISCV64.MillerRabin

namespace VG.Artifacts.RsaKeyGen.RISCV64

def artifacts : List Artifact :=
  direct ++
  (VG.Proof.Variants.MillerRabin.RISCV64.variants.flatMap fun v => MillerRabin.artifacts v)

end VG.Artifacts.RsaKeyGen.RISCV64
