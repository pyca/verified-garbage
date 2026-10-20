module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeDrawCTState
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeDraw
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeSample
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeRound
public import VerifiedGarbage.Impl.Dsa.X86.Generation.DrawWitness
public import VerifiedGarbage.Impl.Dsa.X86.Generation.PrepareExponent
public import VerifiedGarbage.Impl.Dsa.X86.Generation.SampleWitness
public import VerifiedGarbage.Proof.Dsa.X86.RandomTwo
import VerifiedGarbage.Proof.Dsa.X86.Generation.DrawWitnessCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeRoundCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.SampleWitnessCT

/-! # Public draws remain public through copying, sampling, and exponentiation -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86
open VG.Impl.Dsa.X86.Generation

theorem primeDraw_phase_ct (G : PrimeConfig) :
    RelCT isa (Two (PrimeDrawAt G)) (drawWitness G.len G.draw) (Two (PrimeDrawnAt G)) := by
  refine two_post (two_map (fun p => (G, p.used)) (fun _ _ h => ⟨h.ready, h.used⟩) (drawWitness_ct _ _)) ?_
  intro p s R
  refine WP.mono (primeDraw_ok R.ready p.full R.used) fun t ⟨Rt, bytes, _, pointer, count, _, _⟩ => ?_
  exact ⟨Rt, pointer, count.trans R.count, by rw [bytes]; exact R.value⟩

theorem primeSample_phase_ct (G : PrimeConfig) :
    RelCT isa (Two (PrimeDrawnAt G)) (sampleWitness G.len) (Two (PrimeSampledAt G)) := by
  refine two_post (two_map (fun p => (G, p.value)) (fun _ _ h => ⟨rfl, h.ready, h.pointer, h.value⟩)
    (sampleWitness_ct _)) ?_
  intro p s R
  refine WP.mono (primeSample_ok R.ready R.pointer) fun t ⟨Rt, value, flag, _, count, _, _⟩ => ?_
  rw [R.value] at value flag
  exact ⟨Rt, value, flag, count.trans R.count⟩

theorem primeRound_phase_ct (G : PrimeConfig) :
    RelCT isa (Two (PrimeSampledAt G)) (.seq (restoreExponent G.n) (round G.n (2 * G.n)))
      (Two (PrimeAnsweredAt G)) := by
  refine two_post (two_map (fun p => (drawSample G p).1) (fun _ _ h => ⟨h.ready, h.value⟩) (primeRound_ct G)) ?_
  intro p s R
  refine WP.mono (primeRound_ok R.ready) fun t ⟨Rt, answer, controls, _, _⟩ => ?_
  rw [R.value] at answer
  exact ⟨Rt, answer, (controls _ (.inr (.inr rfl))).trans R.flag, (controls _ (.inr (.inl rfl))).trans R.count⟩
end VG.Proof.Dsa.X86.Generation
