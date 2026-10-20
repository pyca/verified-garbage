module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PhaseData
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Sieve
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontAll
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessState
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerStages

/-! # FFDH parameter generation on x86-64: sieve either modulus phase -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64 VG.Proof.MlKem.X86_64

theorem primeCheck_state_ok {p : CandidateP} {used : Nat} {q : Bool} {s : State} {mi : BitVec 64}
    (h : CandidateTape p used s)
    (hg : Good s (off p.B 256) (p.Z - 256) (p.phaseWords q) mi)
    (hp : PhaseHeader p q s)
    (hn : wv s.mem (off p.B 256) (slot (p.phaseWords q) aN) (p.phaseWords q) = p.phaseValue q) :
    WP isa primeCheck s fun t => CandidateTape p used t ∧
      Good t (off p.B 256) (p.Z - 256) (p.phaseWords q) mi ∧ PhaseHeader p q t ∧
      wv t.mem (off p.B 256) (slot (p.phaseWords q) aN) (p.phaseWords q) = p.phaseValue q ∧
      t.zf = some (Spec.Ffdh.primeShape (p.phaseValue q)) ∧
      CandidateSaved p s.mem t.mem ∧ CandidateFrame p s.mem t.mem ∧ Keep mmRegs s t ∧
      Spec.Rsa.bytesAt t.mem p.op p.k = Spec.Rsa.bytesAt s.mem p.op p.k := by
  refine WP.mono (primeCheck_ok hg (h.base.phase_dims q).z (h.base.phase_table_room q)
    (by omega_using [(h.base.phase_room q).1])
    (by omega_using [(h.base.phase_room q).2.1])
    (by rw [hn]; exact h.base.phase_large q)) fun t ⟨hz, hgt, hf, k⟩ => ?_
  have hrs : ∀ r ∈ [(slot (p.phaseWords q) aTab, 2048), (8 * kT0, 8), (8 * kT1, 8), (8 * kT2, 8)],
      r.1 + r.2 ≤ p.Z - 256 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h.base.phase_table_room q
    all_goals
      have hd := (h.base.phase_dims q).z
      change _ ≤ p.Z - 256
      unfold slot hdrBytes at hd
      simp only [kT0, kT1, kT2, sFn]
      omega
  have hl : ∀ r ∈ [(slot (p.phaseWords q) aTab, 2048), (8 * kT0, 8), (8 * kT1, 8), (8 * kT2, 8)],
      136 ≤ r.1 ∨ r.1 + r.2 ≤ 128 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · left; unfold slot hdrBytes; omega
    all_goals dsimp only; decide
  have kk : Keep mmRegs s t := k.mono (by decide)
  refine ⟨h.keep_inner hf hrs kk (by decide), hgt, hp.of_inner h.base hf hrs hl,
    ?_, by simpa only [hn] using hz,
    fun j hj => h.base.inner_header hf hrs j (by omega),
    CandidateFrame.of_scr (h.base.inner_changes hf hrs), kk,
    h.base.output_eq (h.base.inner_changes hf hrs)⟩
  rw [hf.wv_eq (by rng_disj) (by
    have hz := (h.base.phase_dims q).z
    have hs := slot_le (w := p.phaseWords q) (show aN < 8 by decide)
    omega_using [hz, hs, h.base.size64])]
  exact hn

end VG.Proof.Ffdh.X86_64.ParameterCandidate
