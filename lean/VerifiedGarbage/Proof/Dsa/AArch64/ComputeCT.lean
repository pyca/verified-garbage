module

import VerifiedGarbage.Proof.Dsa.AArch64.PublicKeyCT
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
meta import VerifiedGarbage.Proof.Dsa.AArch64.PublicKeyCT
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

def signComputeInputs (p : SchedulePublic) : List (Operand × Nat) :=
  (Core.publicValue, p.layout.pLen) :: (⟨.input .q, .qLen⟩, p.layout.qLen) :: signInputs p

def verifyComputeInputs (p : SchedulePublic) : List (Operand × Nat) :=
  (⟨.input .q, .qLen⟩, p.layout.qLen) :: verifyInputs p

theorem signComputeInputs_stable (p : SchedulePublic) (a : Operand × Nat)
    (ha : a ∈ signComputeInputs p) : a.1.length ≠ .mask ∧ stablePointer a.1.pointer := by
  simp only [signComputeInputs, List.mem_cons] at ha
  rcases ha with rfl | rfl | ha
  · simp [Core.publicValue, stablePointer]
  · change Field.qLen ≠ .mask ∧ Field.q ≠ .mask
    decide
  · exact signInputs_stable p a ha

theorem verifyComputeInputs_stable (p : SchedulePublic) (a : Operand × Nat)
    (ha : a ∈ verifyComputeInputs p) : a.1.length ≠ .mask ∧ stablePointer a.1.pointer := by
  simp only [verifyComputeInputs, List.mem_cons] at ha
  rcases ha with rfl | ha
  · change Field.qLen ≠ .mask ∧ Field.q ≠ .mask
    decide
  · exact verifyInputs_stable p a ha

theorem signCompute_ct (M : Mont) : RelCT isa (Two (PublicKeyPre signComputeInputs))
    (signCompute M.mm) (Two (ScheduleState signComputeInputs)) := by
  have h1 := signingKey_ct M signComputeInputs signComputeInputs_stable
    (by intro p; simp [signComputeInputs, signInputs])
    (by intro p; simp [signComputeInputs]) (by intro p; simp [signComputeInputs])
  have h2 := privateKey_ct M signComputeInputs signComputeInputs_stable
    (by intro p; simp [signComputeInputs, signInputs]) (by intro p; simp [signComputeInputs])
    (by intro p; simp [signComputeInputs, signInputs]) (by intro p; simp [signComputeInputs, signInputs])
  have h3 := coreSignSchedule_ct M signComputeInputs signComputeInputs_stable
    (by intro p a ha; simp [signComputeInputs, ha])
  have h4 := scheduleZero_ct signComputeInputs signComputeInputs_stable (Core.scalar r)
    (fun p => p.layout.qLen) true (by change r < 2 ^ 16; decide) (by trivial) (by decide)
    (fun p => p.layout.widths.1) (by intro p; have := p.layout.widths; omega) (by taint_decide)
  have h5 := scheduleZero_ct signComputeInputs signComputeInputs_stable (Core.scalar s)
    (fun p => p.layout.qLen) true (by change s < 2 ^ 16; decide) (by trivial) (by decide)
    (fun p => p.layout.widths.1) (by intro p; have := p.layout.widths; omega) (by taint_decide)
  unfold signCompute seqs
  refine RelCT.seq h1 (RelCT.seq h2 (RelCT.seq h3 (RelCT.seq (R := Two (ScheduleState signComputeInputs)) ?_ ?_)))
  · exact two_map (fun p => p) (fun p st h =>
      ⟨h, h.1.availableLocal .q r (by decide) (scalar_space (by decide) p)⟩) h4
  · exact two_map (fun p => p) (fun p st h =>
      ⟨h, h.1.availableLocal .q s (by decide) (scalar_space (by decide) p)⟩) h5

theorem verifyCompute_ct (M : Mont) : RelCT isa (Two (PublicKeyPre verifyComputeInputs))
    (verifyCompute M.mm) (Two (ScheduleState verifyComputeInputs)) := by
  have h1 := publicKey_ct M verifyComputeInputs verifyComputeInputs_stable
    (by intro p; simp [verifyComputeInputs, verifyInputs])
    (by intro p; simp [verifyComputeInputs, verifyInputs]) (by intro p; simp [verifyComputeInputs])
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
  unfold verifyCompute seqs
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
