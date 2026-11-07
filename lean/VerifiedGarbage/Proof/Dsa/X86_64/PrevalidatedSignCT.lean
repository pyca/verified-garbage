module

public import VerifiedGarbage.Proof.Dsa.X86_64.PrevalidatedSign
public import VerifiedGarbage.Proof.Dsa.X86_64.BodyCT
public import VerifiedGarbage.Proof.Dsa.X86_64.SigningPublic
public import VerifiedGarbage.Proof.Dsa.X86_64.SigningCT
import VerifiedGarbage.Proof.Dsa.X86_64.FailureCT
import VerifiedGarbage.Proof.Dsa.X86_64.ComputeCT
import VerifiedGarbage.Proof.Dsa.X86_64.CoreSignCT
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleCheckCT
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleCTState
import VerifiedGarbage.Proof.Dsa.X86_64.SignReleaseCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Dsa.X86_64.PrevalidatedSign
meta import VerifiedGarbage.Proof.Dsa.X86_64.BodyCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.SigningPublic
meta import VerifiedGarbage.Proof.Dsa.X86_64.SigningCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.FailureCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.ComputeCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.CoreSignCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleCheckCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleCTState
meta import VerifiedGarbage.Proof.Dsa.X86_64.SignReleaseCT
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # Constant time of an x86-64 DSA signing attempt for a validated private key -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem prevalidatedSignCompute_ct (M : Mont) (Sq : MontS) : RelCT isa (Two (ScheduleState signComputeInputs))
    (PrevalidatedSign.compute Sq.mm M.mm) (Two (ScheduleState signComputeInputs)) := by
  have h1 := scheduleMinus_ct signComputeInputs signComputeInputs_stable .q 2 qMinusTwo (by decide)
    (by intro p; have := p.qGreater; change 2 ≤ p.layout.subgroup; omega)
    (by decide) (by decide) (scalar_space (by decide)) (by taint_decide) (by taint_decide)
  have h2 := scheduleRange_ct signComputeInputs signComputeInputs_stable .q Core.nonce
    (fun p => p.layout.qLen) false (by trivial) (by simp [stablePointer, Core.nonce])
    (fun p => p.layout.widths.1) (fun _ => Nat.le_refl _) (by taint_decide)
  have h3 := coreSignSchedule_ct M Sq signComputeInputs signComputeInputs_stable
    (by intro p a ha; simp [signComputeInputs, ha])
  have h4 := scheduleZero_ct signComputeInputs signComputeInputs_stable (Core.scalar r)
    (fun p => p.layout.qLen) true (by change r < 2 ^ 31; decide) (by trivial) (by decide)
    (fun p => p.layout.widths.1) (by intro p; have := p.layout.widths; omega) (by taint_decide)
  have h5 := scheduleZero_ct signComputeInputs signComputeInputs_stable (Core.scalar s)
    (fun p => p.layout.qLen) true (by change s < 2 ^ 31; decide) (by trivial) (by decide)
    (fun p => p.layout.widths.1) (by intro p; have := p.layout.widths; omega) (by taint_decide)
  unfold PrevalidatedSign.compute seqs
  refine RelCT.seq h1 (RelCT.seq (R := Two (ScheduleState signComputeInputs)) ?_
    (RelCT.seq h3 (RelCT.seq (R := Two (ScheduleState signComputeInputs)) ?_ ?_)))
  · exact two_map (fun p => p) (fun p st h =>
      ⟨h, (h.2.1 (Core.nonce, p.layout.qLen) (by simp [signComputeInputs, signInputs])).active⟩) h2
  · exact two_map (fun p => p) (fun p st h =>
      ⟨h, h.1.availableLocal .q r (by decide) (scalar_space (by decide) p)⟩) h4
  · exact two_map (fun p => p) (fun p st h =>
      ⟨h, h.1.availableLocal .q s (by decide) (scalar_space (by decide) p)⟩) h5

theorem prevalidatedSignComputeRelease_ok (M : Mont) (Sq : MontS) {p : SchedulePublic} {s : State}
    (h : SigningBodyPre p s) :
    WP isa (PrevalidatedSign.compute Sq.mm M.mm) s (ReleasePre p.release) := by
  obtain ⟨hr, ⟨data, yb, qb, ho, _⟩, ⟨valid, hm⟩, hw, hsep⟩ := h
  refine WP.mono (prevalidatedSignCompute_ok M Sq hr p.pGreater p.qGreater p.pOdd p.qOdd p.pFits p.qFits
    data ho.generator ho.privateScalar ho.nonce ho.digest ho.generatorLength ho.privateLength
    ho.nonceLength ho.digestBound hm) fun t ⟨ht, hm, _, _, _, hk⟩ => ?_
  exact ⟨ht.scratch, ht.parent.rdi, ht.fields .out (by decide),
    (ht.fields .qLen (by decide)).trans p.layout.qLength, ⟨_, hm⟩,
    fun i hi => by rw [hk.2.2]; exact hw i hi, hsep⟩

theorem prevalidatedSignBody_ct (M : Mont) (Sq : MontS) :
    RelCT isa (Two SigningBodyPre) (prevalidatedSignBody Sq.mm M.mm) (fun _ _ => True) := by
  refine RelCT.seq (R := Two (fun p : SchedulePublic => ReleasePre p.release)) ?_ ?_
  · refine two_post ((two_map (fun p => p) (fun _ _ h => h.schedule.1) (prevalidatedSignCompute_ct M Sq)).mono
      (fun _ _ h => h) (fun _ _ _ => trivial)) ?_
    exact fun _ _ h => prevalidatedSignComputeRelease_ok M Sq h
  · exact two_map SchedulePublic.release (fun _ _ h => h) signRelease_ct

theorem prevalidatedSignSuccess_ct (M : Mont) (Sq : MontS) :
    RelCT isa (Two (fun c : AcceptedSigningCall => SigningShaped c.val))
      (seqs [SignVerify.workspaces, PrevalidatedSign.compute Sq.mm M.mm,
        SignVerify.writeScalar r false, SignVerify.writeScalar s true, .block SignVerify.result])
      (fun _ _ => True) := by
  refine RelCT.seq signingWorkspaces_ct ?_
  exact (prevalidatedSignBody_ct M Sq).mono (fun _ _ h => signingReady_related h) (fun _ _ h => h)

theorem prevalidatedSignMain_ct (M : Mont) (Sq : MontS) :
    RelCT isa (Two SigningStart) (PrevalidatedSign.sign Sq.mm M.mm) (fun _ _ => True) := by
  apply RelCT.assoc
  refine RelCT.seq signingShape_ct (RelCT.ite ?_ ?_ ?_)
  · rintro s₁ s₂ ⟨reference, h₁, h₂⟩
    exact h₁.branch.trans h₂.branch.symm
  · exact ((two_map SigningCall.failure (fun _ _ h => h.failure) signFailure_ct).mono
      (fun _ _ h => h.1) (fun _ _ h => h))
  · refine (prevalidatedSignSuccess_ct M Sq).mono ?_ (fun _ _ h => h)
    rintro s₁ s₂ ⟨⟨reference, h₁, h₂⟩, hb⟩
    have ha : reference.input.accepted = true := by
      change eval .e s₁ = some false at hb
      rw [h₁.branch] at hb
      cases h : reference.input.accepted <;> simp_all
    exact ⟨⟨reference, ha⟩, h₁, h₂⟩

end VG.Proof.Dsa.X86_64
