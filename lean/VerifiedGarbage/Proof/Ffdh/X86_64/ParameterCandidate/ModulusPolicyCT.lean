module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.StageCTData
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Prepared
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Kernel
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.RoundsCT
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PrepareCT
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PrepareState
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PhaseWitness
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Octets
import Mathlib.Algebra.Group.Nat.Defs

/-! # FFDH parameter generation on x86-64: timing of the complete modulus policy -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Proof.RsaKeyGen.X86_64 (two_bind)

def PhasePrime (q : Bool) (d : CandidatePublic) (s : State) : Prop :=
  PhaseLoaded q d s ∧ d.p.phaseValue q % 2 = 1

def PhasePrepared (q : Bool) (d : CandidatePublic) (s : State) : Prop :=
  CandidateState d s ∧ d.p.phaseValue q % 2 = 1 ∧ ∃ mi,
    ModulusReady s (off d.p.B 256) (d.p.Z - 256) (d.p.phaseWords q) mi (d.p.phaseValue q) ∧ PhaseHeader d.p q s

private theorem prepare_phase (M : Mont) (R : R2Impl M) (q : Bool) (d : CandidatePublic) (s : State) (h : PhasePrime q d s) :
    WP isa (prepareModulus M.mm R.code) s (PhasePrepared q d) := by
  obtain ⟨mi, hg, hp, hn⟩ := h.1.2
  exact WP.mono (prepareModulus_state_ok M R h.1.1.1 hg hp hn h.2)
    fun _ ⟨mi', ht, hr, hp', _, _, k⟩ => ⟨⟨ht, k.2.2.trans h.1.1.2.1, h.1.1.2.2⟩, h.2, mi', hr, hp'⟩

private theorem prepared_rounds (q : Bool) {s₁ s₂ : State} (h : Two (PhasePrepared q) s₁ s₂) : Two RoundsBefore s₁ s₂ := by
  refine two_bind (fun d t₁ t₂ h₁ h₂ => ?_) h
  obtain ⟨mi₁, hr₁, hp₁⟩ := h₁.2.2
  obtain ⟨mi₂, hr₂, hp₂⟩ := h₂.2.2
  have hw : 1 ≤ d.p.phaseWords q := by omega_using [(h₁.1.1.base.phase_room q).1]
  have hi₁ := hr₁.inv
  have hi₂ := hr₂.inv
  have he₁ : (word t₁.mem (off d.p.B 256) (slot (d.p.phaseWords q) aN)).toNat = d.p.phaseValue q % 2 ^ 64 := by
    rw [← wv_mod64 (n := d.p.phaseWords q) _ _ _ hw, hr₁.n]
  have he₂ : (word t₂.mem (off d.p.B 256) (slot (d.p.phaseWords q) aN)).toNat = d.p.phaseValue q % 2 ^ 64 := by
    rw [← wv_mod64 (n := d.p.phaseWords q) _ _ _ hw, hr₂.n]
  rw [he₁] at hi₁
  rw [he₂] at hi₂
  have heq := minv_unique (by rw [Nat.mod_mod_of_dvd _ (by decide)]; exact h₁.2.1) hi₁ hi₂
  cases heq
  let wp := h₁.1.1.base.witnessParams q mi₁ h₁.2.1
  let dp : DrawPublic := ⟨wp, off d.p.rp d.used, d.used, d.p.rand.drop d.used, d.wr⟩
  let pp : PolicyPublic := ⟨dp, d.p.sp, 0, Spec.Ffdh.primeChecks (d.p.phaseBits q)⟩
  have hchecks : 0 < pp.checks ∧ pp.checks < 2 ^ 31 := by
    change 0 < Spec.Ffdh.primeChecks (d.p.phaseBits q) ∧ Spec.Ffdh.primeChecks (d.p.phaseBits q) < 2 ^ 31
    unfold Spec.Ffdh.primeChecks; split <;> decide
  refine ⟨pp, ?_, ?_⟩
  · exact ⟨⟨h₁.1.1.drawState hp₁ h₁.2.1 hr₁, h₁.1.2.1, h₁.1.2.2⟩,
      h₁.1.1.roundRoom h₁.2.1, h₁.1.1.base.sp, hp₁.checks, hchecks.1, hchecks.2⟩
  · exact ⟨⟨h₂.1.1.drawState hp₂ h₁.2.1 hr₂, h₂.1.2.1, h₂.1.2.2⟩,
      h₂.1.1.roundRoom h₁.2.1, h₂.1.1.base.sp, hp₂.checks, hchecks.1, hchecks.2⟩

theorem modulusPolicy_ct (M : Mont) (R : R2Impl M) (K : Kernel) (q : Bool) :
    RelCT isa (Two (PhasePrime q)) (modulusPolicy M.mm R.code K.run) fun _ _ => True := by
  unfold modulusPolicy
  exact RelCT.seq (two_post
    (two_map (fun d : CandidatePublic => d.prep q) (fun _ _ h => h.1.prepare h.2) (prepareModulus_ct M R))
    (prepare_phase M R q)) ((rounds_ct M K).mono (fun _ _ h => prepared_rounds q h) (fun _ _ h => h))

end VG.Proof.Ffdh.X86_64.ParameterCandidate
