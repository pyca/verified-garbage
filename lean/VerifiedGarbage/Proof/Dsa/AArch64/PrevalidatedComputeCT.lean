module

public import VerifiedGarbage.Proof.Dsa.AArch64.ComputeCT
public import VerifiedGarbage.Proof.Dsa.AArch64.PrevalidatedCompute
import VerifiedGarbage.Proof.Dsa.AArch64.PrivateKeyCT
public import VerifiedGarbage.Proof.Dsa.AArch64.CoreSignCT
public import VerifiedGarbage.Proof.Dsa.AArch64.CoreVerifyCT
public import VerifiedGarbage.Proof.Dsa.AArch64.SignCompute
public import VerifiedGarbage.Proof.Dsa.AArch64.VerifyCompute
public import VerifiedGarbage.Proof.Dsa.AArch64.PublicScheduleCT
import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleCheckCT
import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleOperands
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Dsa.AArch64.ComputeCT
public import VerifiedGarbage.Proof.Dsa.AArch64.PrevalidatedCompute
meta import VerifiedGarbage.Proof.Dsa.AArch64.PrivateKeyCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.CoreSignCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.CoreVerifyCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.SignCompute
meta import VerifiedGarbage.Proof.Dsa.AArch64.VerifyCompute
meta import VerifiedGarbage.Proof.Dsa.AArch64.PublicScheduleCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleCheckCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleOperands
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! # Constant time of validation and signing/verification together -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem prevalidatedCompute_ct (M : Mont) : RelCT isa (Two (ScheduleState verifyComputeInputs))
    (Prevalidated.compute M.mm) (Two (ScheduleState verifyComputeInputs)) := by
  have h1 := scheduleMinus_ct verifyComputeInputs verifyComputeInputs_stable .q 2 qMinusTwo (by decide)
    (by intro p; have := p.qGreater; change 2 ≤ p.layout.subgroup; omega)
    (by decide) (by decide) (scalar_space (by decide)) (by taint_decide) (by taint_decide)
  have h2 := scheduleRange_ct verifyComputeInputs verifyComputeInputs_stable .q Core.signatureR
    (fun p => p.layout.qLen) false (by trivial) (by simp [stablePointer, Core.signatureR])
    (fun p => p.layout.widths.1) (fun _ => Nat.le_refl _) (by taint_decide)
  have h3 := scheduleRange_ct verifyComputeInputs verifyComputeInputs_stable .q Core.signatureS
    (fun p => p.layout.qLen) false (by trivial) (by trivial)
    (fun p => p.layout.widths.1) (fun _ => Nat.le_refl _) (by taint_decide)
  have h4 := coreVerifySchedule_ct M verifyComputeInputs verifyComputeInputs_stable
    (by intro p a ha; simp [verifyComputeInputs, ha])
  have h5 := scheduleEqual_ct verifyComputeInputs verifyComputeInputs_stable (Core.scalar u) Core.signatureR
    (fun p => p.layout.qLen) false (by change u < 2 ^ 16; decide) (by trivial) (by trivial)
    (by simp [stablePointer, Core.signatureR]) (by decide)
    (fun p => p.layout.widths.1) (by intro p; have := p.layout.widths; omega) (by taint_decide)
  unfold Prevalidated.compute seqs
  refine RelCT.seq h1 (RelCT.seq (R := Two (ScheduleState verifyComputeInputs)) ?_
    (RelCT.seq (R := Two (ScheduleState verifyComputeInputs)) ?_ (RelCT.seq h4 ?_)))
  · exact two_map (fun p => p) (fun p st h =>
      ⟨h, (h.2.1 (Core.signatureR, p.layout.qLen) (by simp [verifyComputeInputs, verifyInputs])).active⟩) h2
  · exact two_map (fun p => p) (fun p st h =>
      ⟨h, (h.2.1 (Core.signatureS, p.layout.qLen) (by simp [verifyComputeInputs, verifyInputs])).active⟩) h3
  · exact two_map (fun p => p) (fun p st h =>
      ⟨h, h.1.availableLocal .q u (by decide) (scalar_space (by decide) p),
        (h.2.1 (Core.signatureR, p.layout.qLen) (by simp [verifyComputeInputs, verifyInputs])).active⟩) h5

end VG.Proof.Dsa.AArch64
