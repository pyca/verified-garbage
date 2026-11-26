module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Sm4.Contract
import VerifiedGarbage.Proof.Sm4.RISCV64.Scrub
import VerifiedGarbage.Impl.Sm4.RISCV64.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sm4.RISCV64.Lit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SM4 on RISC-V -/

namespace VG.Artifacts.Sm4.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Sm4.expandKeyApi.artifact RISCV64.target {
    code := Impl.Sm4.RISCV64.Fn.expandKey
    verified := Proof.Sm4.RISCV64.Scrub.expandKey_scrubbed },
  Spec.Sm4.ecbEncryptApi.artifact RISCV64.target {
    code := Impl.Sm4.RISCV64.Fn.ecbEncrypt
    verified := Proof.Sm4.RISCV64.Scrub.ecbEncrypt_scrubbed },
  Spec.Sm4.ecbDecryptApi.artifact RISCV64.target {
    code := Impl.Sm4.RISCV64.Fn.ecbDecrypt
    verified := Proof.Sm4.RISCV64.Scrub.ecbDecrypt_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Sm4.RISCV64
