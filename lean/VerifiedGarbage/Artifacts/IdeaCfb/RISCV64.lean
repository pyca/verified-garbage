module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Idea.Cfb
public import VerifiedGarbage.Spec.Idea.CfbFinal
import VerifiedGarbage.Proof.Idea.RISCV64.Scrub
import VerifiedGarbage.Impl.Idea.RISCV64.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Idea.RISCV64.ModesLit
import VerifiedGarbage.Proof.Idea.RISCV64.FbFinalLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # IDEA-CFB64 on RISC-V -/

namespace VG.Artifacts.IdeaCfb.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
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

spec_apis artifacts

end VG.Artifacts.IdeaCfb.RISCV64
