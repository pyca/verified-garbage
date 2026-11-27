module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Blowfish.Contract
import VerifiedGarbage.Proof.Blowfish.RISCV64.Scrub
import VerifiedGarbage.Impl.Blowfish.RISCV64.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Blowfish.RISCV64.Lit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Blowfish on RISC-V -/

namespace VG.Artifacts.Blowfish.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Blowfish.expandKeyApi.artifact RISCV64.target {
    code := Impl.Blowfish.RISCV64.Fn.expandKey
    verified := Proof.Blowfish.RISCV64.Scrub.expandKey_scrubbed },
  Spec.Blowfish.ecbEncryptApi.artifact RISCV64.target {
    code := Impl.Blowfish.RISCV64.Fn.ecbEncrypt
    verified := Proof.Blowfish.RISCV64.Scrub.ecbEncrypt_scrubbed },
  Spec.Blowfish.ecbDecryptApi.artifact RISCV64.target {
    code := Impl.Blowfish.RISCV64.Fn.ecbDecrypt
    verified := Proof.Blowfish.RISCV64.Scrub.ecbDecrypt_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Blowfish.RISCV64
