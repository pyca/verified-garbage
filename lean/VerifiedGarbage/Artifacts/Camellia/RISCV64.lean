module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Camellia.Contract
import VerifiedGarbage.Proof.Camellia.RISCV64.Scrub
import VerifiedGarbage.Impl.Camellia.RISCV64.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Camellia.RISCV64.Lit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Camellia on RISC-V -/

namespace VG.Artifacts.Camellia.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Camellia.expandKeyApi.artifact RISCV64.target {
    code := Impl.Camellia.RISCV64.Fn.expandKey
    verified := Proof.Camellia.RISCV64.Scrub.expandKey_scrubbed },
  Spec.Camellia.ecbEncryptApi.artifact RISCV64.target {
    code := Impl.Camellia.RISCV64.Fn.ecbEncrypt
    verified := Proof.Camellia.RISCV64.Scrub.ecbEncrypt_scrubbed },
  Spec.Camellia.ecbDecryptApi.artifact RISCV64.target {
    code := Impl.Camellia.RISCV64.Fn.ecbDecrypt
    verified := Proof.Camellia.RISCV64.Scrub.ecbDecrypt_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Camellia.RISCV64
