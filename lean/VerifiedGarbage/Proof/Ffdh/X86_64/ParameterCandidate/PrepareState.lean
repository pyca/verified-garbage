module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PhaseData
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Prepared
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessState
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerStages

/-! # FFDH parameter generation on x86-64: prepare the shared primality modulus -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64 VG.Proof.MlKem.X86_64

theorem CandidateBase.modulus_ranges {p : CandidateP} {s : State} (h : CandidateBase p s) (q : Bool) :
    ∀ r ∈ modulusRanges (p.phaseWords q),
      r.1 + r.2 ≤ p.Z - 256 ∧ (136 ≤ r.1 ∨ r.1 + r.2 ≤ 128) := by
  intro r hr
  simp only [modulusRanges, prepareRanges, constantRanges, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at hr
  have hz := (h.phase_dims q).z
  have hx := (h.phase_dims q).x
  rcases hr with (((rfl | rfl) | hr) | (rfl | rfl | rfl | rfl | rfl)) | rfl
  · constructor
    · change 64 ≤ p.Z - 256
      unfold slot hdrBytes at hz; omega
    · right; decide
  · constructor
    · have hs := slot_le (w := p.phaseWords q) (show aOne < 8 by decide)
      omega_using [hs, hz]
    · left; unfold slot hdrBytes; omega
  · refine ⟨Nat.le_trans (r2Ranges_le _ r hr) hz, Or.inl ?_⟩
    simp only [r2Ranges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      simp only [slot, hdrBytes, aAcc, aTmp, aR2, sCnt, sFn] <;> omega
  all_goals refine ⟨?_, Or.inl (by simp only [slot, hdrBytes]; omega_using [])⟩
  all_goals
    simp only [slot, hdrBytes, aAcc, aTmp, aY, aR1, aRm1, aE] at hz hx ⊢
    omega_using [hz, hx]

theorem prepareModulus_state_ok (M : Mont) (R : R2Impl M)
    {p : CandidateP} {used : Nat} {q : Bool} {s : State} {mi : BitVec 64}
    (h : CandidateTape p used s)
    (hg : Good s (off p.B 256) (p.Z - 256) (p.phaseWords q) mi)
    (hp : PhaseHeader p q s)
    (hn : wv s.mem (off p.B 256) (slot (p.phaseWords q) aN) (p.phaseWords q) = p.phaseValue q)
    (ho : p.phaseValue q % 2 = 1) :
    WP isa (prepareModulus M.mm R.code) s fun t => ∃ mi', CandidateTape p used t ∧
      ModulusReady t (off p.B 256) (p.Z - 256) (p.phaseWords q) mi' (p.phaseValue q) ∧
      PhaseHeader p q t ∧ CandidateSaved p s.mem t.mem ∧ CandidateFrame p s.mem t.mem ∧ Keep mmRegs s t := by
  refine WP.mono (prepareModulus_ok M R hg (h.base.phase_dims q) hn ho
    (by omega_using [h.base.phase_large q]) (h.base.phase_wordshape q).1)
    fun t ⟨mi', ht, hf, k⟩ => ?_
  have hrs := fun r hr => (h.base.modulus_ranges q r hr).1
  exact ⟨mi', h.keep_inner hf hrs k (by decide), ht,
    hp.of_inner h.base hf hrs (fun r hr => (h.base.modulus_ranges q r hr).2),
    fun j hj => h.base.inner_header hf hrs j (by omega),
    CandidateFrame.of_scr (h.base.inner_changes hf hrs), k⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate
