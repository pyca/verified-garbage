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
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved

/-! # RSA key generation (FIPS 186-5 A.1.3) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.RsaKeyGen.RISCV64

def direct : List Artifact := [
  Spec.RsaKeyGen.keyInitApi.artifact RISCV64.target (RISCV64.Scrub.scrubOf {
    code := Impl.RsaKeyGen.RISCV64.KeyInit.init
    verified := Proof.RsaKeyGen.RISCV64.KeyInit.init_verified }
    Proof.Rsa.RISCV64.Scrub.keyInitOut)]

def artifacts : List Artifact :=
  direct ++
  (VG.Proof.Variants.MillerRabin.RISCV64.variants.attach.flatMap
    fun (v : { v : Proof.MillerRabin.RISCV64.RoundImpl // v ∈ VG.Proof.Variants.MillerRabin.RISCV64.variants }) => [
    Spec.RsaKeyGen.keySearchApi.artifact RISCV64.target (RISCV64.Scrub.scrubOf {
      suffix := v.1.suffix
      code := Proof.RsaKeyGen.RISCV64.Generate.genCode v.1
      verified := Proof.RsaKeyGen.RISCV64.Generate.gen_verified v.1 }
      (Proof.Rsa.RISCV64.Scrub.keySearchOut Proof.RsaKeyGen.RISCV64.Generate.tables
        Proof.RsaKeyGen.RISCV64.Generate.stackUse)
      Proof.RsaKeyGen.RISCV64.Generate.stackUse (Spec.RsaKeyGen.keySearchSig.retBits 64)
      (Proof.RsaKeyGen.RISCV64.Generate.keySearchSide v.1 v.2))])

end VG.Artifacts.RsaKeyGen.RISCV64
