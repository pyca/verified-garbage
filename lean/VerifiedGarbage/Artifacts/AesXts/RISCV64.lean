module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Xts.Contract
import VerifiedGarbage.Proof.AesXts.RISCV64.Scrub
import VerifiedGarbage.Impl.Aes.RISCV64.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.AesXts.RISCV64.Lit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # XTS-AES (IEEE Std 1619-2007, NIST SP 800-38E) on RISC-V -/

namespace VG.Artifacts.AesXts.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Xts.aesEncryptUnitApi.artifact RISCV64.target {
    code := Impl.Aes.RISCV64.Fn.xtsEncryptUnit
    verified := Proof.AesXts.RISCV64.Scrub.xtsEncryptUnit_scrubbed },
  Spec.Xts.aesDecryptUnitApi.artifact RISCV64.target {
    code := Impl.Aes.RISCV64.Fn.xtsDecryptUnit
    verified := Proof.AesXts.RISCV64.Scrub.xtsDecryptUnit_scrubbed }]

spec_apis artifacts

end VG.Artifacts.AesXts.RISCV64
