module

public import VerifiedGarbage.Proof.Idea.RISCV64.ModesVerified
public import VerifiedGarbage.Proof.Idea.RISCV64.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Idea.RISCV64.ModesLit
import VerifiedGarbage.Proof.Idea.RISCV64.FbFinalLit

/-! # IDEA-CFB64 on RISC-V -/

@[expose] public section

namespace VG.Artifacts.IdeaCfb.RISCV64

def artifacts : List Artifact := [
  Spec.Idea.cfbEncryptApi.artifact RISCV64.target {
    code := Impl.Idea.RISCV64.cfbEncrypt
    verified := Proof.Idea.RISCV64.Modes.cfbEncrypt_verified },
  Spec.Idea.cfbDecryptApi.artifact RISCV64.target {
    code := Impl.Idea.RISCV64.cfbDecrypt
    verified := Proof.Idea.RISCV64.Modes.cfbDecrypt_verified },
  Spec.Idea.cfbEncryptFinalApi.artifact RISCV64.target {
    code := Impl.Idea.RISCV64.cfbEncryptFinal
    verified := Proof.Idea.RISCV64.Modes.cfbEncryptFinal_verified },
  Spec.Idea.cfbDecryptFinalApi.artifact RISCV64.target {
    code := Impl.Idea.RISCV64.cfbDecryptFinal
    verified := Proof.Idea.RISCV64.Modes.cfbDecryptFinal_verified }]

end VG.Artifacts.IdeaCfb.RISCV64
