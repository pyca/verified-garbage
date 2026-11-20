module

public import VerifiedGarbage.Proof.AesSiv.RISCV64.Init
public import VerifiedGarbage.Proof.AesSiv.RISCV64.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # AES-SIV (RFC 5297) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.AesSiv.RISCV64

def artifacts : List Artifact := [
  Spec.Siv.initApi.artifact RISCV64.target {
    code := Impl.AesSiv.RISCV64.Fn.init
    verified := .scrubbed Proof.AesSiv.RISCV64.init_scrubbed },
  Spec.Siv.encryptApi.artifact RISCV64.target {
    code := Impl.AesSiv.RISCV64.Fn.encrypt
    verified := .scrubbed Proof.AesSiv.RISCV64.Scrub.encrypt_scrubbed },
  Spec.Siv.decryptApi.artifact RISCV64.target {
    code := Impl.AesSiv.RISCV64.Fn.decrypt
    verified := .scrubbed Proof.AesSiv.RISCV64.Scrub.decrypt_scrubbed }]

end VG.Artifacts.AesSiv.RISCV64
