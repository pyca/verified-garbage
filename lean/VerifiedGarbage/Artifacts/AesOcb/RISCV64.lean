module

public import VerifiedGarbage.Proof.AesOcb.RISCV64.Init
public import VerifiedGarbage.Proof.AesOcb.RISCV64.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # AES-OCB (RFC 7253) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.AesOcb.RISCV64

def artifacts : List Artifact := [
  Spec.Ocb.initApi.artifact RISCV64.target {
    code := Impl.AesOcb.RISCV64.Fn.init
    verified := Proof.AesOcb.RISCV64.init_scrubbed },
  Spec.Ocb.sealApi.artifact RISCV64.target {
    code := Impl.AesOcb.RISCV64.Fn.«seal»
    verified := Proof.AesOcb.RISCV64.Scrub.seal_scrubbed },
  Spec.Ocb.openApi.artifact RISCV64.target {
    code := Impl.AesOcb.RISCV64.Fn.«open»
    verified := Proof.AesOcb.RISCV64.Scrub.open_scrubbed }]

end VG.Artifacts.AesOcb.RISCV64
