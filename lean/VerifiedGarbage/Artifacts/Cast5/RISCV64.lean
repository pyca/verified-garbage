module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Cast5.Contract
import VerifiedGarbage.Proof.Cast5.RISCV64.Scrub
import VerifiedGarbage.Impl.Cast5.RISCV64.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Cast5.RISCV64.Lit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # CAST5 (RFC 2144) on RISC-V -/

namespace VG.Artifacts.Cast5.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Cast5.expandKeyApi.artifact RISCV64.target {
    code := Impl.Cast5.RISCV64.Fn.expandKey
    verified := Proof.Cast5.RISCV64.Scrub.expandKey_scrubbed },
  Spec.Cast5.ecbEncryptApi.artifact RISCV64.target {
    code := Impl.Cast5.RISCV64.Fn.ecbEncrypt
    verified := Proof.Cast5.RISCV64.Scrub.ecbEncrypt_scrubbed },
  Spec.Cast5.ecbDecryptApi.artifact RISCV64.target {
    code := Impl.Cast5.RISCV64.Fn.ecbDecrypt
    verified := Proof.Cast5.RISCV64.Scrub.ecbDecrypt_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Cast5.RISCV64
