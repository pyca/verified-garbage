module

public import VerifiedGarbage.Proof.Cast5.RISCV64.ModesVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Cast5.RISCV64.ModesLit

/-! # CAST5-CFB artifacts on baseline RISC-V -/

@[expose] public section

namespace VG.Artifacts.Cast5Cfb.RISCV64

def artifacts : List Artifact := [
  Spec.Cast5.cfbEncryptApi.artifact RISCV64.target {
    consts := Impl.Cast5.ecbConsts
    code := Impl.Cast5.RISCV64.cfbEncrypt
    stack := 128
    verified := Proof.Cast5.RISCV64.Modes.cfbEncrypt_verified },
  Spec.Cast5.cfbDecryptApi.artifact RISCV64.target {
    consts := Impl.Cast5.ecbConsts
    code := Impl.Cast5.RISCV64.cfbDecrypt
    stack := 128
    verified := Proof.Cast5.RISCV64.Modes.cfbDecrypt_verified }]

end VG.Artifacts.Cast5Cfb.RISCV64
