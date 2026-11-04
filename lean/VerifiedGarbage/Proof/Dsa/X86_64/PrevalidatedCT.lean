module

public import VerifiedGarbage.Proof.Dsa.X86_64.Prevalidated
public import VerifiedGarbage.Proof.Dsa.X86_64.BodyCT
public import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingPublic
import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingCT
public import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingReadyCT
import VerifiedGarbage.Proof.Dsa.X86_64.ComputeCT
import VerifiedGarbage.Proof.Dsa.X86_64.CoreVerifyCT
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleCheckCT
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleCTState
import VerifiedGarbage.Proof.Dsa.X86_64.BoundaryCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Dsa.X86_64.Prevalidated
meta import VerifiedGarbage.Proof.Dsa.X86_64.BodyCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingPublic
meta import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingReadyCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.ComputeCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.CoreVerifyCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleCheckCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleCTState
meta import VerifiedGarbage.Proof.Dsa.X86_64.BoundaryCT
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # Constant time of x86-64 DSA verification for a validated public key -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem prevalidatedCompute_ct (M : Mont) (Sq : MontS) : RelCT isa (Two (ScheduleState verifyComputeInputs))
    (Prevalidated.compute Sq.mm M.mm) (Two (ScheduleState verifyComputeInputs)) := by
  have h1 := scheduleMinus_ct verifyComputeInputs verifyComputeInputs_stable .q 2 qMinusTwo (by decide)
    (by intro p; have := p.qGreater; change 2 ≤ p.layout.subgroup; omega)
    (by decide) (by decide) (scalar_space (by decide)) (by taint_decide) (by taint_decide)
  have h2 := scheduleRange_ct verifyComputeInputs verifyComputeInputs_stable .q Core.signatureR
    (fun p => p.layout.qLen) false (by trivial) (by simp [stablePointer, Core.signatureR])
    (fun p => p.layout.widths.1) (fun _ => Nat.le_refl _) (by taint_decide)
  have h3 := scheduleRange_ct verifyComputeInputs verifyComputeInputs_stable .q Core.signatureS
    (fun p => p.layout.qLen) false (by trivial) (by trivial)
    (fun p => p.layout.widths.1) (fun _ => Nat.le_refl _) (by taint_decide)
  have h4 := coreVerifySchedule_ct M Sq verifyComputeInputs verifyComputeInputs_stable
    (by intro p a ha; simp [verifyComputeInputs, ha])
  have h5 := scheduleEqual_ct verifyComputeInputs verifyComputeInputs_stable (Core.scalar u) Core.signatureR
    (fun p => p.layout.qLen) false (by change u < 2 ^ 31; decide) (by trivial) (by trivial)
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

theorem prevalidatedComputeReturn_ok (M : Mont) (Sq : MontS) {p : SchedulePublic} {s : State}
    (h : VerifyingBodyPre p s) :
    WP isa (Prevalidated.compute Sq.mm M.mm) s (fun t => t.gpr .rdi = p.layout.base) := by
  obtain ⟨hr, ⟨data, qb, ho, _⟩, ⟨valid, hm⟩⟩ := h
  refine WP.mono (prevalidatedCompute_ok M Sq hr p.pGreater p.qGreater p.pOdd p.qOdd p.pFits p.qFits data
    ho.generator ho.publicValue ho.signatureR ho.signatureS ho.digest
    ho.generatorLength ho.publicLength ho.rLength ho.sLength
    ho.digestBound hm) fun _ h => h.1.parent.rdi

theorem prevalidatedBody_ct (M : Mont) (Sq : MontS) :
    RelCT isa (Two VerifyingBodyPre) (prevalidatedBody Sq.mm M.mm) (fun _ _ => True) := by
  refine RelCT.seq (R := Two (fun p : SchedulePublic => fun t => t.gpr .rdi = p.layout.base)) ?_ ?_
  · refine two_post ((two_map (fun p => p) (fun _ _ h => h.schedule.1) (prevalidatedCompute_ct M Sq)).mono
      (fun _ _ h => h) (fun _ _ _ => trivial)) ?_
    exact fun _ _ h => prevalidatedComputeReturn_ok M Sq h
  · exact two_map (fun p => p.layout.base) (fun _ _ h => h) result_ct

theorem prevalidatedSuccess_ct (M : Mont) (Sq : MontS) :
    RelCT isa (Two (fun c : AcceptedVerifyingCall => VerifyingShaped c.val))
      (seqs [SignVerify.workspaces, Prevalidated.compute Sq.mm M.mm, .block SignVerify.result])
      (fun _ _ => True) := by
  refine RelCT.seq verifyingWorkspaces_ct ?_
  exact (prevalidatedBody_ct M Sq).mono (fun _ _ h => verifyingReady_related h) (fun _ _ h => h)

theorem prevalidatedMain_ct (M : Mont) (Sq : MontS) :
    RelCT isa (Two VerifyingStart) (Prevalidated.verify Sq.mm M.mm) (fun _ _ => True) := by
  apply RelCT.assoc
  refine RelCT.seq verifyingShape_ct (RelCT.ite ?_ ?_ ?_)
  · rintro s₁ s₂ ⟨reference, h₁, h₂⟩
    exact h₁.branch.trans h₂.branch.symm
  · exact ((two_map (fun c : VerifyingCall => c.layout.base) (fun _ _ h => h.rdi) verifyFailure_ct).mono
      (fun _ _ h => h.1) (fun _ _ h => h))
  · refine (prevalidatedSuccess_ct M Sq).mono ?_ (fun _ _ h => h)
    rintro s₁ s₂ ⟨⟨reference, h₁, h₂⟩, hb⟩
    have ha : reference.input.accepted = true := by
      change eval .e s₁ = some false at hb
      rw [h₁.branch] at hb
      cases h : reference.input.accepted <;> simp_all
    exact ⟨⟨reference, ha⟩, h₁, h₂⟩

end VG.Proof.Dsa.X86_64
