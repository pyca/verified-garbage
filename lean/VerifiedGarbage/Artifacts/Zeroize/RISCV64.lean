module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Zeroize.Contract
import VerifiedGarbage.Proof.Zeroize.RISCV64
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Zeroization on RISC-V -/

namespace VG.Artifacts.Zeroize.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Zeroize.zeroizeApi.artifact RISCV64.target {
    code := Impl.Zeroize.RISCV64.zeroize
    verified := Proof.Zeroize.RISCV64.scrubbed }]

spec_apis artifacts

end VG.Artifacts.Zeroize.RISCV64
