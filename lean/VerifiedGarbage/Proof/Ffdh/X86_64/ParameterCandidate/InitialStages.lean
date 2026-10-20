module
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.StageCTData

import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Consume
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.CheckGenerator
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.CheckPrime
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.LoadOutput
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.LeavePhase

/-! # FFDH parameter generation on x86-64: retain the initial candidate through trial checks -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.MlKem.X86_64

def CandidatePublic.afterCandidate (d : CandidatePublic) : CandidatePublic := { d with used := d.p.k }

theorem consume_initial (d : CandidatePublic) (s : State) (h : OuterValue false d s ∧ d.used = 0) :
    WP isa (.block consumeCandidate) s (OuterValue false d.afterCandidate) := by
  have ht : CandidateTape d.p 0 s := by simpa only [h.2] using h.1.1.1.1
  exact WP.mono (consumeCandidate_ok ht h.1.1.2 d.available)
    fun t ⟨ht', _, _, k, hv⟩ => ⟨⟨⟨ht', k.2.2.trans h.1.1.1.2.1, h.1.1.1.2.2⟩,
      (k.gpr (by decide)).trans h.1.1.2⟩, by
        change Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem d.p.op d.p.k) = d.p.P
        rw [hv]; exact h.1.2⟩

def InitialLoaded (d : CandidatePublic) (s : State) : Prop :=
  PhaseLoaded false d s ∧ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem d.p.op d.p.k) = d.p.P

theorem load_initial (d : CandidatePublic) (s : State) (h : PhaseSet false d s) :
    WP isa loadOutput s (InitialLoaded d) := by
  obtain ⟨mi, hg, hp, hv⟩ := h.2
  exact WP.mono (loadOutput_ok h.1.1 hg hp hv)
    fun _ ⟨ht, hgt, hpt, hnt, _, _, k, hbytes⟩ =>
      ⟨⟨⟨ht, k.2.2.trans h.1.2.1, h.1.2.2⟩, mi, hgt, hpt, hnt⟩, by rw [hbytes]; exact hv⟩

def InitialGenerator (d : CandidatePublic) (s : State) : Prop :=
  InitialLoaded d s ∧ s.zf = some (Spec.Ffdh.generationShape d.p.bits d.p.gen d.p.P)

theorem generator_initial (d : CandidatePublic) (s : State) (h : InitialLoaded d s) :
    WP isa generatorPolicy s (InitialGenerator d) := by
  obtain ⟨mi, hg, hp, hn⟩ := h.1.2
  exact WP.mono (generatorCheck_state_ok h.1.1.1 hg hp hn)
    fun _ ⟨ht, hgt, hpt, hnt, hz, hm, k⟩ =>
      ⟨⟨⟨⟨ht, k.2.2.trans h.1.1.2.1, h.1.1.2.2⟩, mi, hgt, hpt, hnt⟩,
        by rw [hm]; exact h.2⟩, hz⟩

def InitialPrime (d : CandidatePublic) (s : State) : Prop :=
  InitialLoaded d s ∧ s.zf = some (Spec.Ffdh.primeShape d.p.P)

theorem prime_initial (d : CandidatePublic) (s : State) (h : InitialLoaded d s) :
    WP isa primeCheck s (InitialPrime d) := by
  obtain ⟨mi, hg, hp, hn⟩ := h.1.2
  exact WP.mono (primeCheck_state_ok h.1.1.1 hg hp hn)
    fun _ ⟨ht, hgt, hpt, hnt, hz, _, _, k, hbytes⟩ =>
      ⟨⟨⟨⟨ht, k.2.2.trans h.1.1.2.1, h.1.1.2.2⟩, mi, hgt, hpt, hnt⟩,
        by rw [hbytes]; exact h.2⟩, hz⟩

theorem leave_initial (d : CandidatePublic) (s : State) (h : InitialLoaded d s) :
    WP isa (.block [VG.Impl.Rsa.X86_64.Crt.leave]) s (OuterValue false d) := by
  obtain ⟨_, hg, hp, _⟩ := h.1.2
  exact WP.mono (leavePhase_ok h.1.1.1 hg.rdi hp.link)
    fun _ ⟨ht, hd, hm, _, _, k⟩ => ⟨⟨⟨ht, k.2.2.trans h.1.1.2.1, h.1.1.2.2⟩, hd⟩,
      by rw [hm]; exact h.2⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate
