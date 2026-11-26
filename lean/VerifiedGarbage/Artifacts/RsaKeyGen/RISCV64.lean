module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.RsaKeyGen.KeySearchContract
import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.MillerRabin.RISCV64.Backend
import VerifiedGarbage.Impl.RsaKeyGen.RISCV64.Fn
import VerifiedGarbage.Proof.Variants.MillerRabin.RISCV64
import VerifiedGarbage.Impl.RsaKeyGen.TrialTable32
import VerifiedGarbage.Proof.Rsa.RISCV64.IbInverse
import VerifiedGarbage.Proof.Divstep.TcSBounds
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # RSA key generation (FIPS 186-5 A.1.3) on RISC-V -/

namespace VG.Artifacts.RsaKeyGen.RISCV64

def direct : List (Artifact RISCV64.target) := [
  Spec.RsaKeyGen.keyInitApi.artifact RISCV64.target {
    code := Impl.RsaKeyGen.RISCV64.KeyInit.Fn.init
    verified := Proof.RsaKeyGen.RISCV64.Fn.init_scrubbed
    publicOutOk := Proof.RsaKeyGen.RISCV64.Fn.init_public }]

public def artifacts : List (Artifact RISCV64.target) :=
  direct ++ Proof.Variants.MillerRabin.RISCV64.variants.map fun (v : Proof.MillerRabin.RISCV64.RoundImpl) =>
    Spec.RsaKeyGen.keySearchApi.artifact RISCV64.target {
      suffix := v.suffix
      code := Impl.RsaKeyGen.RISCV64.Fn.keySearch v.suffix v.code
      verified := Proof.RsaKeyGen.RISCV64.Fn.keySearch_scrubbed v
      publicOutOk := Proof.RsaKeyGen.RISCV64.Fn.keySearch_public v }

spec_apis artifacts

end VG.Artifacts.RsaKeyGen.RISCV64
