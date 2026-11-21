module

public import VerifiedGarbage.Proof.Cast5.RISCV64.Scrub
public import VerifiedGarbage.Impl.Cast5.RISCV64.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Cast5.RISCV64.Lit

/-! # CAST5 (RFC 2144) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Cast5.RISCV64

def artifacts : List Artifact := [
  Spec.Cast5.expandKeyApi.artifact RISCV64.target {
    code := Impl.Cast5.RISCV64.Fn.expandKey
    verified := Proof.Cast5.RISCV64.Scrub.expandKey_scrubbed },
  Spec.Cast5.ecbEncryptApi.artifact RISCV64.target {
    code := Impl.Cast5.RISCV64.Fn.ecbEncrypt
    verified := Proof.Cast5.RISCV64.Scrub.ecbEncrypt_scrubbed },
  Spec.Cast5.ecbDecryptApi.artifact RISCV64.target {
    code := Impl.Cast5.RISCV64.Fn.ecbDecrypt
    verified := Proof.Cast5.RISCV64.Scrub.ecbDecrypt_scrubbed }]

end VG.Artifacts.Cast5.RISCV64
