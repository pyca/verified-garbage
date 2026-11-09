module

public import VerifiedGarbage.Proof.TripleDes.RISCV64.ModesVerified
public import VerifiedGarbage.Proof.TripleDes.RISCV64.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.TripleDes.RISCV64.ModesLit
import VerifiedGarbage.Proof.TripleDes.RISCV64.FbFinalLit

/-! # Triple DES-CFB64 artifacts on baseline RISC-V -/

@[expose] public section

namespace VG.Artifacts.TripleDesCfb.RISCV64

def artifacts : List Artifact := [
  Spec.TripleDes.cfbEncryptApi.artifact RISCV64.target {
    code := Impl.TripleDes.RISCV64.cfbEncrypt
    stack := 944
    verified := Proof.TripleDes.RISCV64.Modes.cfbEncrypt_verified },
  Spec.TripleDes.cfbDecryptApi.artifact RISCV64.target {
    code := Impl.TripleDes.RISCV64.cfbDecrypt
    stack := 944
    verified := Proof.TripleDes.RISCV64.Modes.cfbDecrypt_verified },
  Spec.TripleDes.cfbEncryptFinalApi.artifact RISCV64.target {
    code := Impl.TripleDes.RISCV64.cfbEncryptFinal
    stack := 944
    verified := Proof.TripleDes.RISCV64.Modes.cfbEncryptFinal_verified },
  Spec.TripleDes.cfbDecryptFinalApi.artifact RISCV64.target {
    code := Impl.TripleDes.RISCV64.cfbDecryptFinal
    stack := 944
    verified := Proof.TripleDes.RISCV64.Modes.cfbDecryptFinal_verified }]

end VG.Artifacts.TripleDesCfb.RISCV64
