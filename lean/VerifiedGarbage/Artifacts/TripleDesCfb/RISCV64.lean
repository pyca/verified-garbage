module

public import VerifiedGarbage.Proof.TripleDes.RISCV64.Scrub
public import VerifiedGarbage.Impl.TripleDes.RISCV64.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.TripleDes.RISCV64.ModesLit
import VerifiedGarbage.Proof.TripleDes.RISCV64.FbFinalLit

/-! # Triple DES-CFB64 on RISC-V -/

@[expose] public section

namespace VG.Artifacts.TripleDesCfb.RISCV64

def artifacts : List Artifact := [
  Spec.TripleDes.cfbEncryptApi.artifact RISCV64.target {
    code := Impl.TripleDes.RISCV64.Fn.cfbEncrypt
    verified := .scrubbed Proof.TripleDes.RISCV64.Scrub.cfbEncrypt_scrubbed },
  Spec.TripleDes.cfbDecryptApi.artifact RISCV64.target {
    code := Impl.TripleDes.RISCV64.Fn.cfbDecrypt
    verified := .scrubbed Proof.TripleDes.RISCV64.Scrub.cfbDecrypt_scrubbed },
  Spec.TripleDes.cfbEncryptFinalApi.artifact RISCV64.target {
    code := Impl.TripleDes.RISCV64.Fn.cfbEncryptFinal
    verified := .scrubbed Proof.TripleDes.RISCV64.Scrub.cfbEncryptFinal_scrubbed },
  Spec.TripleDes.cfbDecryptFinalApi.artifact RISCV64.target {
    code := Impl.TripleDes.RISCV64.Fn.cfbDecryptFinal
    verified := .scrubbed Proof.TripleDes.RISCV64.Scrub.cfbDecryptFinal_scrubbed }]

end VG.Artifacts.TripleDesCfb.RISCV64
