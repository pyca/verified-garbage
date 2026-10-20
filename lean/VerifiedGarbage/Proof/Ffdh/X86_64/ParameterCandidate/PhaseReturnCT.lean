module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.ModulusPolicyCT
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PhaseRounds
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.LinkCT
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.ModulusPolicy
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.LeavePhase
import VerifiedGarbage.Proof.Framework.Omega

/-! # FFDH parameter generation on x86-64: public result at a modulus phase boundary -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.Ffdh.ParameterCandidate (checkWitnesses)
open VG.Proof.MillerRabin.X86_64

def policyStatus : Option (Bool × List Byte) → Nat
  | none => 0
  | some (pass, _) => if pass then 1 else 2

def CandidatePublic.decision (d : CandidatePublic) (q : Bool) : Option (Bool × List Byte) :=
  checkWitnesses (d.p.phaseValue q) (Spec.Ffdh.primeChecks (d.p.phaseBits q)) (d.p.rand.drop d.used)

theorem PhaseOutcome.status {p : CandidateP} {used n : Nat} {q : Bool} {m : Mem}
    (h : PhaseOutcome p used n q m) :
    word m p.B (8 * oStatus) = BitVec.ofNat 64 (policyStatus
      (checkWitnesses (p.phaseValue q) (Spec.Ffdh.primeChecks (p.phaseBits q)) (p.rand.drop used))) := by
  cases he : checkWitnesses (p.phaseValue q) (Spec.Ffdh.primeChecks (p.phaseBits q)) (p.rand.drop used) with
  | none =>
    simp only [PhaseOutcome, he] at h
    exact h
  | some ar =>
    obtain ⟨pass, rest⟩ := ar
    simp only [PhaseOutcome, he] at h
    exact h.1

def PhaseDone (q : Bool) (d : CandidatePublic) (s : State) : Prop :=
  ∃ n, n ≤ (d.p.rand.drop d.used).length ∧ CandidateTape d.p (d.used + n) s ∧
    s.gpr .rdi = off d.p.B 256 ∧ word s.mem (off d.p.B 256) (8 * VG.Impl.Rsa.X86_64.Crt.sLink) = d.p.B ∧
    PhaseOutcome d.p d.used n q s.mem ∧ s.wr = d.wr ∧ InnerKW d.p.B d.wr

def PhaseReturned (q : Bool) (d : CandidatePublic) (s : State) : Prop :=
  (∃ n, CandidateTape d.p (d.used + n) s ∧ s.gpr .rdi = d.p.B ∧ PhaseOutcome d.p d.used n q s.mem) ∧
    s.wr = d.wr ∧ InnerKW d.p.B d.wr ∧ s.zf = some (decide (policyStatus (d.decision q) = 1))

theorem modulusPolicy_done (M : Mont) (R : R2Impl M) (K : Kernel) (q : Bool) (d : CandidatePublic) (s : State)
    (h : PhasePrime q d s) : WP isa (modulusPolicy M.mm R.code K.run) s (PhaseDone q d) := by
  obtain ⟨mi, hg, hp, hn⟩ := h.1.2
  exact WP.mono (modulusPolicy_ok M R K h.1.1.1 hg hp hn h.2)
    fun _ ⟨n, hn', ht, hd, hl, hr, _, _, k⟩ => ⟨n, hn', ht, hd, hl, hr, k.2.2.trans h.1.1.2.1, h.1.1.2.2⟩

theorem PhaseDone.link {q : Bool} {d : CandidatePublic} {s : State} (h : PhaseDone q d s) :
    LinkHeader ⟨d.p.B, d.wr⟩ s := by
  obtain ⟨_, _, _, hd, hl, _, hw, hk⟩ := h
  exact ⟨hk, hd, hw, fun e he => by simp only [List.mem_singleton] at he; subst e; exact hl⟩

private theorem returned (q : Bool) (d : CandidatePublic) (s : State) (h : PhaseDone q d s) :
    WP isa leaveStatus s (PhaseReturned q d) := by
  obtain ⟨n, _, ht, hd, hl, hr, hw, hk⟩ := h
  have hs : word s.mem d.p.B (8 * oStatus) = BitVec.ofNat 64 (policyStatus (d.decision q)) := hr.status
  have hflag : (BitVec.ofNat 64 (policyStatus (d.decision q)) == 1) = decide (policyStatus (d.decision q) = 1) := by
    cases d.decision q with
    | none => rfl
    | some ar => obtain ⟨pass, rest⟩ := ar; cases pass <;> rfl
  exact WP.mono (leaveStatus_ok ht hd hl) fun t ⟨htt, hdt, hzt, hmt, _, _, k⟩ =>
    ⟨⟨n, htt, hdt, hr.congr (by rw [hmt])⟩, k.2.2.trans hw, hk, by simpa only [hs, hflag] using hzt⟩

theorem leaveReturned_ct (q : Bool) : RelCT isa (Two (PhaseDone q)) leaveStatus (Two (PhaseReturned q)) :=
  two_post (two_map (fun d : CandidatePublic => (⟨d.p.B, d.wr⟩ : LinkPublic)) (fun _ _ h => h.link) leaveStatus_ct)
    (returned q)

theorem PhaseReturned.outer {q : Bool} {d : CandidatePublic} {s : State} (h : PhaseReturned q d s) :
    OuterHeader d.outer s := by
  obtain ⟨n, ht, hd, _⟩ := h.1
  let d' : CandidatePublic := { d with used := d.used + n }
  have hs : OuterState d' s := ⟨⟨ht, h.2.1, h.2.2.1⟩, hd⟩
  exact hs.header

end VG.Proof.Ffdh.X86_64.ParameterCandidate
