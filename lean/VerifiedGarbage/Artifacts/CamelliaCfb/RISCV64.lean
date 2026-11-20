module

public import VerifiedGarbage.Proof.Camellia.RISCV64.Scrub
public import VerifiedGarbage.Impl.Camellia.RISCV64.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Camellia.RISCV64.ModesLit
import VerifiedGarbage.Proof.Camellia.RISCV64.FbFinalLit

/-! # Camellia-CFB128 on RISC-V -/

@[expose] public section

namespace VG.Artifacts.CamelliaCfb.RISCV64

def artifacts : List Artifact := [
  Spec.Camellia.cfbEncryptApi.artifact RISCV64.target {
    code := Impl.Camellia.RISCV64.Fn.cfbEncrypt
    verified := .scrubbed Proof.Camellia.RISCV64.Scrub.cfbEncrypt_scrubbed },
  Spec.Camellia.cfbDecryptApi.artifact RISCV64.target {
    code := Impl.Camellia.RISCV64.Fn.cfbDecrypt
    verified := .scrubbed Proof.Camellia.RISCV64.Scrub.cfbDecrypt_scrubbed },
  Spec.Camellia.cfbEncryptFinalApi.artifact RISCV64.target {
    code := Impl.Camellia.RISCV64.Fn.cfbEncryptFinal
    verified := .scrubbed Proof.Camellia.RISCV64.Scrub.cfbEncryptFinal_scrubbed },
  Spec.Camellia.cfbDecryptFinalApi.artifact RISCV64.target {
    code := Impl.Camellia.RISCV64.Fn.cfbDecryptFinal
    verified := .scrubbed Proof.Camellia.RISCV64.Scrub.cfbDecryptFinal_scrubbed }]

end VG.Artifacts.CamelliaCfb.RISCV64
