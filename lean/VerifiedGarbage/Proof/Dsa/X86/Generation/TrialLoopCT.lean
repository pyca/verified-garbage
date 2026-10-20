module
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialStep
public import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialCTState
public import VerifiedGarbage.Proof.Dsa.X86.RandomTwo
import VerifiedGarbage.Proof.Dsa.X86.Generation.BoundedLoopCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialStepCT

/-! # Both runs stop at the same first trial divisor -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86
open VG.Impl.Dsa.X86.Generation VG.Impl.RsaKeyGen

def TrialFinishedAt (len entries : Nat) (p : TrialPublic) (t : State) : Prop :=
  ∃ s, TrialInputs s p.base p.input p.table len entries ∧ trialValue s p.input len = p.value ∧
    TrialDone s p.base p.input len entries t

theorem trialLoop_ct (len entries : Nat) :
    RelCT isa (Two fun p s => p.index < entries ∧ TrialAt len entries p s)
      (.loop (trialCheckStep len entries) .ne) (Two (TrialFinishedAt len entries)) := by
  have step : ∀ (p : TrialPublic) i s, i < entries → TrialAt len entries {p with index := i} s →
      WP isa (trialCheckStep len entries) s fun t =>
        isa.eval .ne t = some (Bool.not (decide (p.value % tabEntry i = 0 ∨ i + 1 = entries))) ∧
        (Bool.not (decide (p.value % tabEntry i = 0 ∨ i + 1 = entries)) = true →
          i + 1 < entries ∧ TrialAt len entries {p with index := i + 1} t) ∧
        (Bool.not (decide (p.value % tabEntry i = 0 ∨ i + 1 = entries)) = false → TrialFinishedAt len entries p t) := by
    rintro p i t hi ⟨s, R, value, I⟩
    refine WP.mono (trialCheckStep_ok R hi I) fun u ⟨zf, result⟩ => ?_
    change u.zf = some (decide (trialValue s p.input len % tabEntry i = 0 ∨ i + 1 = entries)) at zf
    rw [value] at zf
    refine ⟨by simp only [eval, zf, Option.map_some], ?_, ?_⟩
    · intro more
      rcases result with ⟨done, _⟩ | ⟨_, hi', I'⟩
      · simp_all
      · exact ⟨hi', s, R, value, I'⟩
    · intro done
      rcases result with ⟨_, D⟩ | ⟨more, _, _⟩
      · exact ⟨s, R, value, D⟩
      · simp_all
  have ct := two_bounded_loop (Φ := fun p i => TrialAt len entries {p with index := i})
    (Ψ := TrialFinishedAt len entries) (fun _ => entries)
    (fun p i => Bool.not (decide (p.value % tabEntry i = 0 ∨ i + 1 = entries)))
    (two_map (fun (p : TrialPublic × Nat) => {p.1 with index := p.2}) (fun _ _ h => h)
      (trialCheckStep_ct len entries)) step
  exact two_map (fun p : TrialPublic => (p, p.index)) (fun _ _ h => h) ct
end VG.Proof.Dsa.X86.Generation
