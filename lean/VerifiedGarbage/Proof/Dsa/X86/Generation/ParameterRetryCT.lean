module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ParameterAnswerCT

/-! # Seed rejection has a public next witness position -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

def ParameterPublic.retry (p : ParameterPublic) : Bool :=
  match p.expected with | some (none, _) => true | _ => false

def ParameterPublic.nextUsed (p : ParameterPublic) : Nat :=
  match p.expected with | some (_, rest) => p.plan.witnesses.bytes.length - rest.length | _ => 0

theorem parameterAnswered_status {plen qlen : Nat} {p : ParameterPublic} {s : State}
    (H : ParameterAnswered plen qlen p s) :
    ∃ W, SearchContext p.plan W s ∧ (W 19 == 3) = p.retry ∧
      (p.retry = true → ParameterBefore plen qlen
        ⟨p.plan, p.seedUsed + p.plan.geometry.qLen, p.nextUsed, H.2.2.2,
          by unfold ParameterPublic.nextUsed; split <;> omega⟩ s) := by
  obtain ⟨⟨_, W, used, R, seed, cursor, bound, result, _⟩, pl, ql, room⟩ := H
  refine ⟨W, R, ?_, ?_⟩
  · rcases result with ⟨status, expected⟩ | ⟨status, expected⟩ | ⟨_, status, expected, _⟩ <;>
      simp only [status, ParameterPublic.retry, expected] <;> rfl
  · intro retry
    rcases result with ⟨status, expected⟩ | ⟨status, expected⟩ | ⟨_, status, expected, _⟩
    · simp only [ParameterPublic.retry, expected, Bool.false_eq_true] at retry
    · have next : p.nextUsed = used := by
        simp only [ParameterPublic.nextUsed, expected, List.length_drop]
        omega
      exact ⟨⟨W, R, seed, by simpa only [next] using cursor⟩, pl, ql⟩
    · simp only [ParameterPublic.retry, expected, Bool.false_eq_true] at retry
end VG.Proof.Dsa.X86.Generation
