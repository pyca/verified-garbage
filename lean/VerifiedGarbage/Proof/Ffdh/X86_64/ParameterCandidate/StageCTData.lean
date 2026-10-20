module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PhaseData
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.OuterCT
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PrepareCTData
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerStages

/-! # FFDH parameter generation on x86-64: public candidate phase boundaries -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64 VG.Proof.RsaKeyGen.X86_64

structure CandidatePublic where
  p : CandidateP
  used : Nat
  wr : List Region
  available : p.k ≤ p.rand.length

def CandidateState (d : CandidatePublic) (s : State) : Prop :=
  CandidateTape d.p d.used s ∧ s.wr = d.wr ∧ InnerKW d.p.B d.wr

def OuterState (d : CandidatePublic) (s : State) : Prop := CandidateState d s ∧ s.gpr .rdi = d.p.B

def CandidatePublic.outer (d : CandidatePublic) : OuterPublic :=
  ⟨d.p.B, d.wr, d.p.op, d.p.k, d.p.up, d.p.bits, 0, d.p.rp⟩

theorem OuterState.header {d : CandidatePublic} {s : State} (h : OuterState d s) : OuterHeader d.outer s := by
  refine ⟨h.1.2.2.kw, h.2, h.1.2.1, ?_⟩
  intro e he
  simp only [CandidatePublic.outer, outerSlots, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  all_goals exact h.1.1.base.hdr _ (by simp [CandidateP.headers])

def OuterValue (q : Bool) (d : CandidatePublic) (s : State) : Prop :=
  OuterState d s ∧ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem d.p.op d.p.k) = d.p.phaseValue q

def PhaseSet (q : Bool) (d : CandidatePublic) (s : State) : Prop :=
  CandidateState d s ∧ ∃ mi,
    Good s (off d.p.B 256) (d.p.Z - 256) (d.p.phaseWords q) mi ∧ PhaseHeader d.p q s ∧
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem d.p.op d.p.k) = d.p.phaseValue q

def PhaseLoaded (q : Bool) (d : CandidatePublic) (s : State) : Prop :=
  CandidateState d s ∧ ∃ mi,
    Good s (off d.p.B 256) (d.p.Z - 256) (d.p.phaseWords q) mi ∧ PhaseHeader d.p q s ∧
      wv s.mem (off d.p.B 256) (slot (d.p.phaseWords q) aN) (d.p.phaseWords q) = d.p.phaseValue q

def CandidatePublic.inner (d : CandidatePublic) (q : Bool) : InnerPublic :=
  ⟨d.p.B, d.p.phaseWords q, d.wr, d.p.op, d.p.k, BitVec.ofNat 64 d.p.gen⟩

def CandidatePublic.prep (d : CandidatePublic) (q : Bool) : PreparePublic :=
  ⟨d.p.B, d.p.Z, d.p.phaseWords q, d.p.phaseValue q, d.wr⟩

theorem PhaseLoaded.prepare {q : Bool} {d : CandidatePublic} {s : State} (h : PhaseLoaded q d s)
    (ho : d.p.phaseValue q % 2 = 1) : PrepareBefore (d.prep q) s := by
  obtain ⟨mi, hg, _, hn⟩ := h.2
  refine ⟨⟨mi, hg, h.1.1.base.phase_dims q, ?_, h.1.2.1, h.1.2.2⟩, hn, ho, ?_,
    h.1.1.base.phase_wordshape q |>.1⟩
  · change slot (d.p.phaseWords q) 28 ≤ d.p.Z - 256
    omega_using [(h.1.1.base.phase_room q).2.2]
  · change 1 < d.p.phaseValue q
    omega_using [h.1.1.base.phase_large q]

end VG.Proof.Ffdh.X86_64.ParameterCandidate
