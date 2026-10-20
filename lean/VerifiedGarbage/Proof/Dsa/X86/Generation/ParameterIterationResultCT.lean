module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ParameterRetryCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.TapeState

/-! # Public seed retries strictly advance the finite seed tape -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86 VG.Impl.Dsa.X86.Generation

def ParameterPublic.again (p : ParameterPublic) : Bool := Bool.not p.exhausted && p.retry

theorem ParameterPublic.nextBound (p : ParameterPublic) : p.nextUsed ≤ p.plan.witnesses.bytes.length := by
  unfold ParameterPublic.nextUsed
  split <;> omega

def ParameterIterationResult (plen qlen : Nat) (p : ParameterPublic) (s : State) : Prop :=
  eval .e s = some p.again ∧ (p.again = true → ∃ bound : p.seedUsed + p.plan.geometry.qLen ≤ p.plan.seeds.bytes.length,
    ParameterBefore plen qlen ⟨p.plan, p.seedUsed + p.plan.geometry.qLen, p.nextUsed, bound, p.nextBound⟩ s)

theorem parameterIteration_result {H : Hash} (Khash : HashOK H) (F : KeyRandom.CheckCall.CheckFn)
    {plen qlen : Nat} {p : ParameterPublic} {s : State}
    (digest : H.D = qlen) (final : H.F = qlen)
    (hash : ∀ bs, Khash.SH.H.hash bs = Spec.Dsa.seedHash (8 * qlen) bs)
    (hashSize : ∀ bs, (Spec.Dsa.seedHash (8 * qlen) bs).length = qlen)
    (Hpre : ParameterBefore plen qlen p s) :
    WP isa (tapeIteration seedTape qlen (parameterBody H plen qlen (finishDomain F.name F.code plen qlen))) s
      (ParameterIterationResult plen qlen p) := by
  unfold tapeIteration
  refine WP.seq (WP.mono (parameter_check Hpre) fun a A => ?_)
  by_cases exhausted : p.plan.seeds.bytes.length - p.seedUsed < p.plan.geometry.qLen
  · have again : p.again = false := by simp [ParameterPublic.again, ParameterPublic.exhausted, exhausted]
    refine WP.ite true (by change a.cf = some true; simpa [ParameterPublic.exhausted, exhausted] using A.2)
      (fun _ => ?_) (fun he => Bool.noConfusion he)
    obtain ⟨⟨W, R, _⟩, _⟩ := A.1
    refine WP.mono (tapeExhausted_ok R.arena.frame R.representation) fun t ⟨zf, _, _, _, _⟩ => ?_
    exact ⟨by simpa only [eval, again] using zf, by simp only [again, Bool.false_eq_true, false_implies]⟩
  · have available : ParameterAvailable plen qlen p a := ⟨A.1, by have := p.seedBound; omega⟩
    refine WP.ite false (by change a.cf = some false; simpa [ParameterPublic.exhausted, exhausted] using A.2)
      (fun he => Bool.noConfusion he) (fun _ => ?_)
    refine WP.seq (WP.mono (parameter_take available) fun b B => ?_)
    refine WP.seq (WP.mono (parameter_answer Khash F digest final hash hashSize B) fun c C => ?_)
    obtain ⟨W, R, status, next⟩ := parameterAnswered_status C
    refine WP.mono (tapeStatus_ok R.arena.frame R.representation) fun t ⟨zf, mem, K⟩ => ?_
    have again : p.again = p.retry := by simp [ParameterPublic.again, ParameterPublic.exhausted, exhausted]
    refine ⟨by change t.zf = some p.again; rw [zf, status, again], ?_⟩
    intro retry
    obtain ⟨⟨Wt, Rt, seed, used⟩, pl, ql⟩ := next (again ▸ retry)
    exact ⟨C.2.2.2, ⟨Wt, Rt.congr mem K (by decide), seed, used⟩, pl, ql⟩
end VG.Proof.Dsa.X86.Generation
