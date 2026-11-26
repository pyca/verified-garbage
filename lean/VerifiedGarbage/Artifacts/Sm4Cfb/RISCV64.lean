module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Sm4.Cfb
public import VerifiedGarbage.Spec.Sm4.CfbFinal
import VerifiedGarbage.Proof.Sm4.RISCV64.Scrub
import VerifiedGarbage.Impl.Sm4.RISCV64.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sm4.RISCV64.ModesLit
import VerifiedGarbage.Proof.Sm4.RISCV64.FbFinalLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SM4-CFB128 on RISC-V -/

namespace VG.Artifacts.Sm4Cfb.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Sm4.cfbEncryptApi.artifact RISCV64.target {
    code := Impl.Sm4.RISCV64.Fn.cfbEncrypt
    verified := Proof.Sm4.RISCV64.Scrub.cfbEncrypt_scrubbed },
  Spec.Sm4.cfbDecryptApi.artifact RISCV64.target {
    code := Impl.Sm4.RISCV64.Fn.cfbDecrypt
    verified := Proof.Sm4.RISCV64.Scrub.cfbDecrypt_scrubbed },
  Spec.Sm4.cfbEncryptFinalApi.artifact RISCV64.target {
    code := Impl.Sm4.RISCV64.Fn.cfbEncryptFinal
    verified := Proof.Sm4.RISCV64.Scrub.cfbEncryptFinal_scrubbed },
  Spec.Sm4.cfbDecryptFinalApi.artifact RISCV64.target {
    code := Impl.Sm4.RISCV64.Fn.cfbDecryptFinal
    verified := Proof.Sm4.RISCV64.Scrub.cfbDecryptFinal_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Sm4Cfb.RISCV64
