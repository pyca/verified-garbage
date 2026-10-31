module

public import VerifiedGarbage.Proof.Idea.RISCV64.ModesVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Idea.RISCV64.ModesLit

/-! # IDEA-CFB64 artifacts on baseline RISC-V -/

@[expose] public section

namespace VG.Artifacts.IdeaCfb.RISCV64

def artifacts : List Artifact := [
  Spec.Idea.cfbEncryptApi.artifact RISCV64.target {
    code := Impl.Idea.RISCV64.cfbEncrypt
    stack := 64
    verified := Proof.Idea.RISCV64.Modes.cfbEncrypt_verified },
  Spec.Idea.cfbDecryptApi.artifact RISCV64.target {
    code := Impl.Idea.RISCV64.cfbDecrypt
    stack := 64
    verified := Proof.Idea.RISCV64.Modes.cfbDecrypt_verified }]

end VG.Artifacts.IdeaCfb.RISCV64
