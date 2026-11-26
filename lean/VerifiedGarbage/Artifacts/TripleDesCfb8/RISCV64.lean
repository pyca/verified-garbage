module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.TripleDes.Cfb8
import VerifiedGarbage.Proof.TripleDes.RISCV64.Scrub
import VerifiedGarbage.Impl.TripleDes.RISCV64.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.TripleDes.RISCV64.ModesLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Triple DES-CFB8 on RISC-V -/

namespace VG.Artifacts.TripleDesCfb8.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.TripleDes.cfb8EncryptApi.artifact RISCV64.target {
    code := Impl.TripleDes.RISCV64.Fn.cfb8Encrypt
    verified := Proof.TripleDes.RISCV64.Scrub.cfb8Encrypt_scrubbed },
  Spec.TripleDes.cfb8DecryptApi.artifact RISCV64.target {
    code := Impl.TripleDes.RISCV64.Fn.cfb8Decrypt
    verified := Proof.TripleDes.RISCV64.Scrub.cfb8Decrypt_scrubbed }]

spec_apis artifacts

end VG.Artifacts.TripleDesCfb8.RISCV64
