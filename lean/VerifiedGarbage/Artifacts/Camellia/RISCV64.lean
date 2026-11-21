module

public import VerifiedGarbage.Proof.Camellia.RISCV64.Scrub
public import VerifiedGarbage.Impl.Camellia.RISCV64.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Camellia.RISCV64.Lit

/-! # Camellia on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Camellia.RISCV64

def artifacts : List Artifact := [
  Spec.Camellia.expandKeyApi.artifact RISCV64.target {
    code := Impl.Camellia.RISCV64.Fn.expandKey
    verified := Proof.Camellia.RISCV64.Scrub.expandKey_scrubbed },
  Spec.Camellia.ecbEncryptApi.artifact RISCV64.target {
    code := Impl.Camellia.RISCV64.Fn.ecbEncrypt
    verified := Proof.Camellia.RISCV64.Scrub.ecbEncrypt_scrubbed },
  Spec.Camellia.ecbDecryptApi.artifact RISCV64.target {
    code := Impl.Camellia.RISCV64.Fn.ecbDecrypt
    verified := Proof.Camellia.RISCV64.Scrub.ecbDecrypt_scrubbed }]

end VG.Artifacts.Camellia.RISCV64
