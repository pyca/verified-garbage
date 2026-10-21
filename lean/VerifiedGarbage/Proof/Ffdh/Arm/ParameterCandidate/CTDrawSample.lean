module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessState
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTBase
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTSampleWitness
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTStackBlocks
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTPolicy
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.DrawHead
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessMemory
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessTape

/-! Public entropy offsets determine the entire native witness import trace. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch

structure DrawPoint where
  params : WitnessParams
  used : Nat
  passed : Nat

def DrawStart (p : DrawPoint) (s : State) : Prop :=
  WitnessState p.params p.used p.passed s ∧ p.used + (p.params.bits + 7) / 8 ≤ p.params.bytes.length

private def drawSampleData (p : DrawPoint) : WitnessSampleData :=
  ⟨⟨p.params.base, p.params.capacity, p.params.words, p.params.bits⟩,
    p.params.tape + BitVec.ofNat 32 p.used⟩

private theorem drawSampleHead_ok (p : DrawPoint) (s : State) (h : DrawStart p s) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.drawHead s (WitnessSampleStart (drawSampleData p)) := by
  refine WP.mono (drawHead_ok h.1 h.2) ?_
  rintro t ⟨ctx, base, source, count, _, _⟩
  exact ⟨⟨ctx.ready base, ctx.saved.space, ctx.bitsPositive, ctx.bitsBound,
    by simpa only [witnessValues, drawSampleData] using ctx.saved.saved 44 (by simp [witnessSlots])⟩,
    ctx.stackScratch, ctx.bitsFit, ctx.source_fits h.2, ctx.source_read h.2, ctx.source_separate h.2,
    source, count⟩

theorem drawSample_ct : RelCT isa (Two DrawStart)
    VG.Impl.Ffdh.Arm.ParameterCandidate.drawSample (fun _ _ => True) := by
  have headTrace : RelCT isa (Two DrawStart) VG.Impl.Ffdh.Arm.ParameterCandidate.drawHead (fun _ _ => True) :=
    (drawArgs_ct.seq (save_ct .r1 40)).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)
  exact (two_post headTrace drawSampleHead_ok).seq
    (sampleWitness_ct.mono (fun _ _ ⟨p, left, right, sp⟩ => ⟨drawSampleData p, left, right, sp⟩) (fun _ _ h => h))

end VG.Proof.Ffdh.Arm.ParameterCandidate
