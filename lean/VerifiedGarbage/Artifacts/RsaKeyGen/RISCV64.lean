module

public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Key.Verified
public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.SearchInit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Rsa.RISCV64.Instances
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # RSA key generation (FIPS 186-5 A.1.3) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.RsaKeyGen.RISCV64

def artifacts : List Artifact := [
  Spec.RsaKeyGen.keyApi.artifact RISCV64.target {
    code := Impl.RsaKeyGen.RISCV64.Key.code
    verified := Proof.RsaKeyGen.RISCV64.Key.key_verified },
  Spec.RsaKeyGen.primeInitApi.artifact RISCV64.target {
    code := Impl.RsaKeyGen.RISCV64.SearchInit.init
    verified := Proof.RsaKeyGen.RISCV64.SearchInit.init_verified }]

end VG.Artifacts.RsaKeyGen.RISCV64
