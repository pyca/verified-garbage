module

public import VerifiedGarbage.Proof.TripleDes.RISCV64.Scrub
public import VerifiedGarbage.Impl.TripleDes.RISCV64.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.TripleDes.RISCV64.ModesLit

/-! # Triple DES-CFB8 on RISC-V -/

@[expose] public section

namespace VG.Artifacts.TripleDesCfb8.RISCV64

def artifacts : List Artifact := [
  Spec.TripleDes.cfb8EncryptApi.artifact RISCV64.target {
    code := Impl.TripleDes.RISCV64.Fn.cfb8Encrypt
    verified := .scrubbed Proof.TripleDes.RISCV64.Scrub.cfb8Encrypt_scrubbed },
  Spec.TripleDes.cfb8DecryptApi.artifact RISCV64.target {
    code := Impl.TripleDes.RISCV64.Fn.cfb8Decrypt
    verified := .scrubbed Proof.TripleDes.RISCV64.Scrub.cfb8Decrypt_scrubbed }]

end VG.Artifacts.TripleDesCfb8.RISCV64
