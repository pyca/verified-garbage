module

public import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Stages

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Scalar
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Scalar

theorem laneReg_zero : ∀ i < 25, laneReg i = .x0 ↔ i = 0 := by decide +kernel

end VG.Proof.Sha3.AArch64.Scalar
