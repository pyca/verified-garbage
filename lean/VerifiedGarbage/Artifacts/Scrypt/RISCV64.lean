module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Scrypt.Contract
import VerifiedGarbage.Proof.Scrypt.RISCV64.BlockMix
import VerifiedGarbage.Proof.Scrypt.RISCV64.RoMix
import VerifiedGarbage.Proof.Scrypt.RISCV64.Whole.Verified
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Scrypt.RISCV64.Scrub
import VerifiedGarbage.Impl.Scrypt.RISCV64.Fn
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # scrypt (RFC 7914) on RISC-V -/

namespace VG.Artifacts.Scrypt.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Scrypt.scryptApi.artifact RISCV64.target {
    code := Impl.Scrypt.RISCV64.Fn.scrypt Proof.Scrypt.RISCV64.Whole.pbkName
      Proof.Scrypt.RISCV64.Whole.pbkCode
    verified := Proof.Scrypt.RISCV64.Scrub.scrypt_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Scrypt.RISCV64
