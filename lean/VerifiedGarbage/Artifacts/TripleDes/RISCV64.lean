module

public import VerifiedGarbage.Proof.TripleDes.RISCV64.Scrub
public import VerifiedGarbage.Impl.TripleDes.RISCV64.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.TripleDes.RISCV64.FunctionsLit
import VerifiedGarbage.Proof.TripleDes.RISCV64.Bitsliced.Lit

/-! # Triple DES on RISC-V -/

@[expose] public section

namespace VG.Artifacts.TripleDes.RISCV64

def artifacts : List Artifact := [
  Spec.TripleDes.expandKeyApi.artifact RISCV64.target {
    code := Impl.TripleDes.RISCV64.Fn.expandKey
    verified := Proof.TripleDes.RISCV64.Scrub.expandKey_scrubbed },
  Spec.TripleDes.ecbEncryptApi.artifact RISCV64.target {
    code := Impl.TripleDes.RISCV64.Fn.ecbEncrypt
    verified := Proof.TripleDes.RISCV64.Scrub.ecbEncrypt_scrubbed },
  Spec.TripleDes.ecbDecryptApi.artifact RISCV64.target {
    code := Impl.TripleDes.RISCV64.Fn.ecbDecrypt
    verified := Proof.TripleDes.RISCV64.Scrub.ecbDecrypt_scrubbed }]

end VG.Artifacts.TripleDes.RISCV64
