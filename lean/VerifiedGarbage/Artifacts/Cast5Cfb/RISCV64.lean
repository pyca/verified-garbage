module

public import VerifiedGarbage.Proof.Cast5.RISCV64.Scrub
public import VerifiedGarbage.Impl.Cast5.RISCV64.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Cast5.RISCV64.ModesLit
import VerifiedGarbage.Proof.Cast5.RISCV64.FbFinalLit

/-! # CAST5-CFB64 on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Cast5Cfb.RISCV64

def artifacts : List Artifact := [
  Spec.Cast5.cfbEncryptApi.artifact RISCV64.target {
    code := Impl.Cast5.RISCV64.Fn.cfbEncrypt
    verified := Proof.Cast5.RISCV64.Scrub.cfbEncrypt_scrubbed },
  Spec.Cast5.cfbDecryptApi.artifact RISCV64.target {
    code := Impl.Cast5.RISCV64.Fn.cfbDecrypt
    verified := Proof.Cast5.RISCV64.Scrub.cfbDecrypt_scrubbed },
  Spec.Cast5.cfbEncryptFinalApi.artifact RISCV64.target {
    code := Impl.Cast5.RISCV64.Fn.cfbEncryptFinal
    verified := Proof.Cast5.RISCV64.Scrub.cfbEncryptFinal_scrubbed },
  Spec.Cast5.cfbDecryptFinalApi.artifact RISCV64.target {
    code := Impl.Cast5.RISCV64.Fn.cfbDecryptFinal
    verified := Proof.Cast5.RISCV64.Scrub.cfbDecryptFinal_scrubbed }]

end VG.Artifacts.Cast5Cfb.RISCV64
