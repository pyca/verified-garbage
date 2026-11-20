module

public import VerifiedGarbage.Proof.Blowfish.RISCV64.Scrub
public import VerifiedGarbage.Impl.Blowfish.RISCV64.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Blowfish.RISCV64.Lit

/-! # Blowfish on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Blowfish.RISCV64

def artifacts : List Artifact := [
  Spec.Blowfish.expandKeyApi.artifact RISCV64.target {
    code := Impl.Blowfish.RISCV64.Fn.expandKey
    verified := .scrubbed Proof.Blowfish.RISCV64.Scrub.expandKey_scrubbed },
  Spec.Blowfish.ecbEncryptApi.artifact RISCV64.target {
    code := Impl.Blowfish.RISCV64.Fn.ecbEncrypt
    verified := .scrubbed Proof.Blowfish.RISCV64.Scrub.ecbEncrypt_scrubbed },
  Spec.Blowfish.ecbDecryptApi.artifact RISCV64.target {
    code := Impl.Blowfish.RISCV64.Fn.ecbDecrypt
    verified := .scrubbed Proof.Blowfish.RISCV64.Scrub.ecbDecrypt_scrubbed }]

end VG.Artifacts.Blowfish.RISCV64
