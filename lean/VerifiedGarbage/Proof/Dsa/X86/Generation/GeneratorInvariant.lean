module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.GeneratorSearchMemory
public import VerifiedGarbage.Proof.Dsa.X86.Generation.TapeIteration

/-! # Generator-loop invariant and exact successful or exhausted outcome -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

def GeneratorInvariant (P : GeneratorSearchPlan) (expected : Option Nat) (initial : State)
    (used : Nat) (s : State) : Prop :=
  ∃ W, GeneratorSearchMemory P W s ∧ W 20 = BitVec.ofNat 32 used ∧
    expected = P.remaining used ∧ Frame P.changed initial.mem s.mem ∧ s.rd = initial.rd ∧ s.wr = initial.wr

def GeneratorFinished (P : GeneratorSearchPlan) (expected : Option Nat) (initial s : State) : Prop :=
  ∃ W, GeneratorSearchMemory P W s ∧
    ((W 19 = 3 ∧ expected = none) ∨
      ∃ value, W 19 = 1 ∧ expected = some value ∧
        Spec.Rsa.bytesAt s.mem ((generatorOutputPointer P.parent).setWidth 64) P.core.len =
          Spec.Dsa.encodeBE P.core.len value) ∧
    Frame P.changed initial.mem s.mem ∧ s.rd = initial.rd ∧ s.wr = initial.wr

theorem generatorInvariant_stable (P : GeneratorSearchPlan) (expected : Option Nat)
    (initial : State) (used : Nat) : TapeStable (GeneratorInvariant P expected initial used) := by
  rintro s t ⟨W, R, usedValue, remaining, O, rd, wr⟩ mem K
  exact ⟨W, R.congr mem K (by decide), usedValue, remaining, by rw [mem]; exact O,
    K.2.1.trans rd, K.2.2.trans wr⟩

theorem generatorFinished_stable (P : GeneratorSearchPlan) (expected : Option Nat)
    (initial : State) : TapeStable (GeneratorFinished P expected initial) := by
  rintro s t ⟨W, R, result, O, rd, wr⟩ mem K
  refine ⟨W, R.congr mem K (by decide), ?_, by rw [mem]; exact O, K.2.1.trans rd, K.2.2.trans wr⟩
  rcases result with fail | ⟨value, status, answer, bytes⟩
  · exact Or.inl fail
  · exact Or.inr ⟨value, status, answer, by rw [mem]; exact bytes⟩

theorem generator_done {P : GeneratorSearchPlan} {expected : Option Nat} {initial : State}
    {used : Nat} {s t : State} {W : Nat → BitVec 32}
    (I : GeneratorInvariant P expected initial used s) (exhausted : P.tape.length - used < P.core.len)
    (rep : FrameWords s.mem P.frame W)
    (repT : FrameWords t.mem P.frame (frameUpdate W 19 3))
    (O : Outside P.frame 76 4 s.mem t.mem) (K : Keeps [.eax] s t) :
    GeneratorFinished P expected initial t := by
  obtain ⟨Wi, Ri, _, remaining, Oi, rd, wr⟩ := I
  have R := Ri.relabel rep
  have Rt := R.control repT (by
    intro i hi hx
    have ne : i ≠ 19 := by intro eq; subst i; simp at hx
    simp only [frameUpdate, ite_eq_right ne]) O (by unfold frameBytes; decide) K (by decide)
  exact ⟨_, Rt, Or.inl ⟨by simp only [frameUpdate, ite_true], remaining.trans (P.remaining_done exhausted)⟩,
    Oi.trans (generator_search_frame O (by unfold frameBytes; decide)), K.2.1.trans rd, K.2.2.trans wr⟩
end VG.Proof.Dsa.X86.Generation
