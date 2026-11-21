module

public import VerifiedGarbage.Proof.Scrypt.RISCV64.BlockMix
public import VerifiedGarbage.Proof.Scrypt.RISCV64.RoMix
public import VerifiedGarbage.Proof.Scrypt.RISCV64.Whole.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Scrypt.RISCV64.Scrub
public import VerifiedGarbage.TCB.RISCV64.Print
public import VerifiedGarbage.Impl.Scrypt.RISCV64.Fn

/-! # scrypt (RFC 7914) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Scrypt.RISCV64

def artifacts : List Artifact := [
  Spec.Scrypt.scryptApi.artifact RISCV64.target {
    code := Impl.Scrypt.RISCV64.Fn.scrypt Proof.Scrypt.RISCV64.Whole.pbkName
      Proof.Scrypt.RISCV64.Whole.pbkCode
    verified := Proof.Scrypt.RISCV64.Scrub.scrypt_scrubbed }]

end VG.Artifacts.Scrypt.RISCV64
