module

public import VerifiedGarbage.Proof.Idea.RISCV64.Scrub
public import VerifiedGarbage.Impl.Idea.RISCV64.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Idea.RISCV64.ModesLit
import VerifiedGarbage.Proof.Idea.RISCV64.FbFinalLit

/-! # IDEA-CFB64 on RISC-V -/

@[expose] public section

namespace VG.Artifacts.IdeaCfb.RISCV64

def artifacts : List Artifact := [
  Spec.Idea.cfbEncryptApi.artifact RISCV64.target {
    code := Impl.Idea.RISCV64.Fn.cfbEncrypt
    verified := Proof.Idea.RISCV64.Scrub.cfbEncrypt_scrubbed },
  Spec.Idea.cfbDecryptApi.artifact RISCV64.target {
    code := Impl.Idea.RISCV64.Fn.cfbDecrypt
    verified := Proof.Idea.RISCV64.Scrub.cfbDecrypt_scrubbed },
  Spec.Idea.cfbEncryptFinalApi.artifact RISCV64.target {
    code := Impl.Idea.RISCV64.Fn.cfbEncryptFinal
    verified := Proof.Idea.RISCV64.Scrub.cfbEncryptFinal_scrubbed },
  Spec.Idea.cfbDecryptFinalApi.artifact RISCV64.target {
    code := Impl.Idea.RISCV64.Fn.cfbDecryptFinal
    verified := Proof.Idea.RISCV64.Scrub.cfbDecryptFinal_scrubbed }]

end VG.Artifacts.IdeaCfb.RISCV64
