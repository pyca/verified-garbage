module

public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.KeyInit
public import VerifiedGarbage.Spec.RsaKeyGen.KeySearchContract
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # RSA key generation (FIPS 186-5 A.1.3) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.RsaKeyGen.RISCV64

def artifacts : List Artifact := [
  Spec.RsaKeyGen.keyInitApi.artifact RISCV64.target {
    code := Impl.RsaKeyGen.RISCV64.KeyInit.init
    verified := Proof.RsaKeyGen.RISCV64.KeyInit.init_verified }]

end VG.Artifacts.RsaKeyGen.RISCV64
