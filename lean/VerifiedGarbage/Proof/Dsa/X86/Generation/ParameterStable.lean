module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ParameterState
import VerifiedGarbage.Proof.Dsa.X86.Generation.SampleMemory
import VerifiedGarbage.Proof.Framework.Offset
import Mathlib.Tactic.Attr.Core
import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchSlots

/-! # Seed-controller updates preserve search results and public input tapes -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.X86.Generation

theorem parameter_frame {P : SearchContextPlan} {s t : Mem} {d n : Nat}
    (O : Outside P.geometry.frameBase d n s t) (room : d + n ≤ VG.Impl.Dsa.X86.Generation.frameBytes) :
    Frame (parameterWrites P.geometry) s t :=
  (sampleOutside_frame O (by unfold VG.Impl.Dsa.X86.Generation.frameBytes at room; omega)).sub (by
    intro r hr; obtain rfl := List.mem_singleton.mp hr
    exact ⟨⟨P.geometry.frameBase, VG.Impl.Dsa.X86.Generation.frameBytes⟩, by simp [parameterWrites], Offset.sub_base _ room⟩)

theorem parameterInvariant_stable (P : SearchContextPlan) (expected : Option Spec.Dsa.Params)
    (initial : State) (used : Nat) : TapeStable (ParameterInvariant P expected initial used) := by
  rintro s t ⟨W, witnessUsed, R, seed, cursor, bound, seedBound, remaining, O, rd, wr⟩ mem K
  exact ⟨W, witnessUsed, R.congr mem K (by decide), seed, cursor, bound, seedBound, remaining,
    by rw [mem]; exact O, K.2.1.trans rd, K.2.2.trans wr⟩

theorem parameterFinished_stable (P : SearchContextPlan) (expected : Option Spec.Dsa.Params)
    (initial : State) : TapeStable (ParameterFinished P expected initial) := by
  rintro s t ⟨W, R, result, O, rd, wr⟩ mem K
  refine ⟨W, R.congr mem K (by decide), ?_, by rw [mem]; exact O, K.2.1.trans rd, K.2.2.trans wr⟩
  rcases result with failed | ⟨params, status, expected, bytes⟩
  · exact .inl failed
  · exact .inr ⟨params, status, expected, by rw [mem]; exact bytes⟩

theorem parameter_done {P : SearchContextPlan} {expected : Option Spec.Dsa.Params} {initial : State}
    {used : Nat} {s t : State} {W : Nat → BitVec 32}
    (I : ParameterInvariant P expected initial used s) (exhausted : P.seeds.bytes.length - used < P.geometry.qLen)
    (rep : FrameWords s.mem P.geometry.frameBase W)
    (repT : FrameWords t.mem P.geometry.frameBase (frameUpdate W 19 3))
    (O : Outside P.geometry.frameBase 76 4 s.mem t.mem) (K : Keeps [.eax] s t) :
    ParameterFinished P expected initial t := by
  obtain ⟨_, witnessUsed, Ri, _, _, _, _, remaining, Oi, rd, wr⟩ := I
  have R := Ri.relabel rep
  have Rt := R.slot (by decide) (by decide) repT O K (by decide)
  exact ⟨_, Rt, .inl ⟨.inr rfl, remaining.trans (parameterRemaining_done P witnessUsed exhausted)⟩,
    Oi.trans (parameter_frame O (by unfold VG.Impl.Dsa.X86.Generation.frameBytes; decide)), K.2.1.trans rd, K.2.2.trans wr⟩
end VG.Proof.Dsa.X86.Generation
