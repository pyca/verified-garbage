module
public meta import VerifiedGarbage.Proof.Framework.X86.RelCT
public meta import VerifiedGarbage.Proof.Dsa.X86.Generation.RoundCompareCT
public import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Spec.Weierstrass.Point
public import VerifiedGarbage.Proof.Dsa.X86.Generation.RoundCTState
import VerifiedGarbage.Proof.Dsa.X86.Generation.RoundCompareCT

/-! # Square-loop branches depend only on the public terminal comparisons -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86
open VG.Impl.Dsa.X86.Generation

theorem roundStep_ct (n : Nat) :
    RelCT isa (Two (RoundAt n)) (roundStep n) (fun _ _ => True) := by
  unfold roundStep
  refine RelCT.seq (roundSquare_phase_ct n) ?_
  apply two_ite (fun _ _ _ hs ht => by simp only [eval, hs.2, ht.2])
  · refine two_taint [.edi] ?_ (by taint_decide)
    intro p s t hs ht
    exact roundCore_pins n (roundSquared p) s t hs.1.1.1 ht.1.1.1
  · refine two_taint [.edi] ?_ (by taint_decide)
    intro p s t hs ht
    exact roundCore_pins n (roundSquared p) s t hs.1.1.1 ht.1.1.1
end VG.Proof.Dsa.X86.Generation
