module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Cast5.Cfb
public import VerifiedGarbage.Spec.Cast5.CfbFinal
import VerifiedGarbage.Proof.Cast5.RISCV64.Scrub
import VerifiedGarbage.Impl.Cast5.RISCV64.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Cast5.RISCV64.ModesLit
import VerifiedGarbage.Proof.Cast5.RISCV64.FbFinalLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # CAST5-CFB64 on RISC-V -/

namespace VG.Artifacts.Cast5Cfb.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Cast5.cfbEncryptApi.artifact RISCV64.target {
    code := Impl.Cast5.RISCV64.Fn.cfbEncrypt
    verified := Proof.Cast5.RISCV64.Scrub.cfbEncrypt_scrubbed },
  Spec.Cast5.cfbDecryptApi.artifact RISCV64.target {
    code := Impl.Cast5.RISCV64.Fn.cfbDecrypt
    verified := Proof.Cast5.RISCV64.Scrub.cfbDecrypt_scrubbed },
  Spec.Cast5.cfbEncryptFinalApi.artifact RISCV64.target {
    code := Impl.Cast5.RISCV64.Fn.cfbEncryptFinal
    verified := Proof.Cast5.RISCV64.Scrub.cfbEncryptFinal_scrubbed },
  Spec.Cast5.cfbDecryptFinalApi.artifact RISCV64.target {
    code := Impl.Cast5.RISCV64.Fn.cfbDecryptFinal
    verified := Proof.Cast5.RISCV64.Scrub.cfbDecryptFinal_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Cast5Cfb.RISCV64
