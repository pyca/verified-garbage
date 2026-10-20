module
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Spec.Weierstrass.Point
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeDrawCTState
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeResultCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeDrawPhasesCT

/-! # One complete witness iteration leaks only the public input draw and counters -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86
open VG.Impl.Dsa.X86.Generation

def primeResultPublic (G : PrimeConfig) (p : PrimeDrawPublic G) : PrimeResultPublic :=
  ⟨G.base, G.size, p.uniform, (drawSample G p).2, drawPassed G p⟩

theorem primeDrawRound_ct (G : PrimeConfig) : RelCT isa (Two (PrimeDrawAt G))
    (primeDrawRound G.len G.draw G.checks) (fun _ _ => True) := by
  refine RelCT.seq (primeDraw_phase_ct G) (RelCT.seq (primeSample_phase_ct G)
    (RelCT.seq (primeRound_phase_ct G) (two_map (primeResultPublic G) ?_ (primeRoundResult_ct G.checks ?_))))
  · intro p s R
    exact ⟨⟨R.ready.context.scr, G.flagRoom, p.bound, R.flag, R.count⟩, R.answer⟩
  · unfold PrimeConfig.checks Spec.Dsa.primeChecks; split <;> decide
end VG.Proof.Dsa.X86.Generation
