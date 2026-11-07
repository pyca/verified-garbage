module

public import VerifiedGarbage.Proof.Cast5.RISCV64.ModesVerified
public import VerifiedGarbage.Proof.Cast5.RISCV64.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Cast5.RISCV64.ModesLit
import VerifiedGarbage.Proof.Cast5.RISCV64.FbFinalLit

/-! # CAST5-CFB artifacts on baseline RISC-V -/

@[expose] public section

namespace VG.Artifacts.Cast5Cfb.RISCV64

def artifacts : List Artifact := [
  Spec.Cast5.cfbEncryptApi.artifact RISCV64.target {
    code := Impl.Cast5.RISCV64.cfbEncrypt
    stack := 128
    verified := Proof.Cast5.cfbEncrypt_keyed Proof.Cast5.RISCV64.Modes.cfbEncrypt_verified },
  Spec.Cast5.cfbDecryptApi.artifact RISCV64.target {
    code := Impl.Cast5.RISCV64.cfbDecrypt
    stack := 128
    verified := Proof.Cast5.cfbDecrypt_keyed Proof.Cast5.RISCV64.Modes.cfbDecrypt_verified },
  Spec.Cast5.cfbEncryptFinalApi.artifact RISCV64.target {
    code := Impl.Cast5.RISCV64.cfbEncryptFinal
    stack := 128
    verified := Proof.Cast5.cfbEncryptFinal_keyed Proof.Cast5.RISCV64.Modes.cfbEncryptFinal_verified },
  Spec.Cast5.cfbDecryptFinalApi.artifact RISCV64.target {
    code := Impl.Cast5.RISCV64.cfbDecryptFinal
    stack := 128
    verified := Proof.Cast5.cfbDecryptFinal_keyed Proof.Cast5.RISCV64.Modes.cfbDecryptFinal_verified }]

end VG.Artifacts.Cast5Cfb.RISCV64
