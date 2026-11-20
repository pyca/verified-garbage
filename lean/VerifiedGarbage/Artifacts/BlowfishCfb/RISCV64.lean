module

public import VerifiedGarbage.Proof.Blowfish.RISCV64.Scrub
public import VerifiedGarbage.Impl.Blowfish.RISCV64.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Blowfish.RISCV64.ModesLit
import VerifiedGarbage.Proof.Blowfish.RISCV64.FbFinalLit

/-! # Blowfish-CFB64 on RISC-V -/

@[expose] public section

namespace VG.Artifacts.BlowfishCfb.RISCV64

def artifacts : List Artifact := [
  Spec.Blowfish.cfbEncryptApi.artifact RISCV64.target {
    code := Impl.Blowfish.RISCV64.Fn.cfbEncrypt
    verified := .scrubbed Proof.Blowfish.RISCV64.Scrub.cfbEncrypt_scrubbed },
  Spec.Blowfish.cfbDecryptApi.artifact RISCV64.target {
    code := Impl.Blowfish.RISCV64.Fn.cfbDecrypt
    verified := .scrubbed Proof.Blowfish.RISCV64.Scrub.cfbDecrypt_scrubbed },
  Spec.Blowfish.cfbEncryptFinalApi.artifact RISCV64.target {
    code := Impl.Blowfish.RISCV64.Fn.cfbEncryptFinal
    verified := .scrubbed Proof.Blowfish.RISCV64.Scrub.cfbEncryptFinal_scrubbed },
  Spec.Blowfish.cfbDecryptFinalApi.artifact RISCV64.target {
    code := Impl.Blowfish.RISCV64.Fn.cfbDecryptFinal
    verified := .scrubbed Proof.Blowfish.RISCV64.Scrub.cfbDecryptFinal_scrubbed }]

end VG.Artifacts.BlowfishCfb.RISCV64
