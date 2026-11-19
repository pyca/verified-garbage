module

public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.KeyInit
public import VerifiedGarbage.Spec.RsaKeyGen.KeySearchContract
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Rsa.RISCV64.Scrub
public import VerifiedGarbage.TCB.RISCV64.Print
public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Backend
public import VerifiedGarbage.Impl.RsaKeyGen.TrialTable32
public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Generate.Verified
public import VerifiedGarbage.Proof.Rsa.RISCV64.IbInverse
public import VerifiedGarbage.Proof.Divstep.TcSBounds
public import VerifiedGarbage.Proof.Variants.MillerRabin.RISCV64

/-! # RSA key generation (FIPS 186-5 A.1.3) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.RsaKeyGen.RISCV64

def direct : List Artifact := [
  Spec.RsaKeyGen.keyInitApi.artifact RISCV64.target (RISCV64.Scrub.withScrub {
    code := Impl.RsaKeyGen.RISCV64.KeyInit.init
    verified := Proof.RsaKeyGen.RISCV64.KeyInit.init_verified }
    Proof.Rsa.RISCV64.Scrub.keyInitOut)]

def artifacts : List Artifact :=
  direct ++
  (VG.Proof.Variants.MillerRabin.RISCV64.variants.flatMap fun (v : Proof.MillerRabin.RISCV64.RoundImpl) => [
    Spec.RsaKeyGen.keySearchApi.artifact RISCV64.target (RISCV64.Scrub.withScrub {
      suffix := v.suffix
      code := Proof.RsaKeyGen.RISCV64.Generate.genCode v
      verified := Proof.RsaKeyGen.RISCV64.Generate.gen_verified v }
      (Proof.Rsa.RISCV64.Scrub.keySearchOut Proof.RsaKeyGen.RISCV64.Generate.tables
        Proof.RsaKeyGen.RISCV64.Generate.stackUse))])

end VG.Artifacts.RsaKeyGen.RISCV64
