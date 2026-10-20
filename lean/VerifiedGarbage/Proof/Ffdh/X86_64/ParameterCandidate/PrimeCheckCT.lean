module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.StageCTData
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Sieve
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.CheckPrime
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.StageCTData
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Sieve
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.CheckPrime
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # FFDH parameter generation on x86-64: timing of either modulus's sieve -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.MlKem.X86_64 VG.Proof.RsaKeyGen.X86_64

theorem PhaseLoaded.header {q : Bool} {d : CandidatePublic} {s : State} (h : PhaseLoaded q d s) :
    InnerHeader (d.inner q) s := by
  obtain ⟨_, hg, _, _⟩ := h.2
  exact ⟨h.1.2.2, good_hp hg h.1.2.1⟩

def OddChecked (q : Bool) (d : CandidatePublic) (s : State) : Prop :=
  PhaseLoaded q d s ∧ s.zf = some (decide (d.p.phaseValue q % 2 = 1))

private theorem odd_checked (q : Bool) (d : CandidatePublic) (s : State) (h : PhaseLoaded q d s) :
    WP isa (.block oddTest) s (OddChecked q d) := by
  obtain ⟨mi, hg, hp, hn⟩ := h.2
  refine WP.mono (oddTest_ok hg (h.1.1.base.phase_dims q).z
    (by omega_using [(h.1.1.base.phase_room q).1])) fun t ⟨hz, hm, k⟩ => ?_
  have ht := (h.1.1.same_mem hm k (by decide)).1
  have hgt : Good t (off d.p.B 256) (d.p.Z - 256) (d.p.phaseWords q) mi :=
    ⟨hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi, by rw [hm]; exact hg.hdr⟩
  exact ⟨⟨⟨ht, k.2.2.trans h.1.2.1, h.1.2.2⟩, mi, hgt,
    ⟨by rw [hm]; exact hp.bits, by rw [hm]; exact hp.len,
      by rw [hm]; exact hp.checks, by rw [hm]; exact hp.link⟩,
    by rw [hm]; exact hn⟩, by simpa only [hn] using hz⟩

theorem primeCheck_ct (q : Bool) : RelCT isa (Two (PhaseLoaded q)) primeCheck fun _ _ => True := by
  unfold primeCheck
  refine RelCT.seq (two_post
    (two_map (fun d : CandidatePublic => d.inner q) (fun _ _ h => h.header) inner_oddTest_ct)
    (odd_checked q)) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => by simp [eval, h₁.2, h₂.2]) ?_
    (two_taint [] (pins_nil _) (by taint_decide))
  exact two_map (fun d : CandidatePublic => d.inner q) (fun _ _ h => h.1.1.header) inner_sieve_ct

def PhaseChecked (q : Bool) (d : CandidatePublic) (s : State) : Prop :=
  PhaseLoaded q d s ∧ s.zf = some (Spec.Ffdh.primeShape (d.p.phaseValue q))

theorem prime_checked (q : Bool) (d : CandidatePublic) (s : State) (h : PhaseLoaded q d s) :
    WP isa primeCheck s (PhaseChecked q d) := by
  obtain ⟨mi, hg, hp, hn⟩ := h.2
  exact WP.mono (primeCheck_state_ok h.1.1 hg hp hn)
    fun t ⟨ht, hgt, hpt, hnt, hz, _, _, k, _⟩ =>
      ⟨⟨⟨ht, k.2.2.trans h.1.2.1, h.1.2.2⟩, mi, hgt, hpt, hnt⟩, hz⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate
