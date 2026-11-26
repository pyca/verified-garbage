module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.TripleDes.Contract
import VerifiedGarbage.Proof.TripleDes.RISCV64.Scrub
import VerifiedGarbage.Impl.TripleDes.RISCV64.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.TripleDes.RISCV64.FunctionsLit
import VerifiedGarbage.Proof.TripleDes.RISCV64.Bitsliced.Lit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Triple DES on RISC-V -/

namespace VG.Artifacts.TripleDes.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.TripleDes.expandKeyApi.artifact RISCV64.target {
    code := Impl.TripleDes.RISCV64.Fn.expandKey
    verified := Proof.TripleDes.RISCV64.Scrub.expandKey_scrubbed },
  Spec.TripleDes.ecbEncryptApi.artifact RISCV64.target {
    code := Impl.TripleDes.RISCV64.Fn.ecbEncrypt
    verified := Proof.TripleDes.RISCV64.Scrub.ecbEncrypt_scrubbed },
  Spec.TripleDes.ecbDecryptApi.artifact RISCV64.target {
    code := Impl.TripleDes.RISCV64.Fn.ecbDecrypt
    verified := Proof.TripleDes.RISCV64.Scrub.ecbDecrypt_scrubbed }]

spec_apis artifacts

end VG.Artifacts.TripleDes.RISCV64
