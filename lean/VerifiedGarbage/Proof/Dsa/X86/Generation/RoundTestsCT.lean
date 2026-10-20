module
public meta import VerifiedGarbage.Proof.Framework.X86.RelCT
public meta import VerifiedGarbage.Proof.Dsa.X86.Generation.RoundLoopCT
public import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Spec.Weierstrass.Point
import VerifiedGarbage.Proof.Dsa.X86.Generation.RoundResult
public import VerifiedGarbage.Proof.Dsa.X86.Generation.RoundCTState
import VerifiedGarbage.Proof.Dsa.X86.Generation.RoundCompareCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.RoundLoopCT

/-! # Initial terminal values and exhausted square counts are public branches -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

theorem roundAccept_ct (n : Nat) : RelCT isa (Two (RoundAt n)) (.block roundAccept) (Two (RoundCoreAt n)) := by
  refine two_piece [.edi] (fun p s t hs ht => roundCore_pins n p s t hs.1 ht.1) (by taint_decide) ?_
  intro p s R
  exact WP.mono (roundAccept_ok R.1) fun _ ⟨Rt, _, _, _⟩ => Rt

theorem roundCountTest_ct (n : Nat) : RelCT isa (Two (RoundAt n)) (.block roundCountTest)
    (Two fun p s => RoundAt n p s ∧ s.zf = some (decide (p.count = 0))) := by
  refine two_piece [.edi] (fun p s t hs ht => roundCore_pins n p s t hs.1 ht.1) (by taint_decide) ?_
  intro p s R
  refine WP.mono (roundCountTest_ok R.1 R.2.2.2 R.2.2.1) fun t ⟨zf, mem, K⟩ => ?_
  exact ⟨⟨R.1.unchanged mem K (by decide) (by decide), by rw [mem]; exact R.2.1,
    by rw [mem]; exact R.2.2.1, R.2.2.2⟩, zf⟩

theorem roundRemaining_ct (n : Nat) : RelCT isa (Two (RoundAt n))
    (.seq (.block roundCountTest) (.ite .e (.block []) (.loop (roundStep n) .ne))) (Two (RoundCoreAt n)) := by
  refine RelCT.seq (roundCountTest_ct n) ?_
  apply two_ite (fun _ _ _ hs ht => by simp only [eval, hs.2, ht.2])
  · exact RelCT.nil (fun _ _ => two_mono (fun _ _ h => h.1.1.1))
  · refine (roundLoop_ct n).mono (fun _ _ => two_mono ?_) (fun _ _ h => h)
    intro p s h
    have nonzero : p.count ≠ 0 := by simpa only [eval, h.1.2, Option.some.injEq, decide_eq_false_iff_not] using h.2
    exact ⟨by omega, h.1.1⟩

theorem roundTests_ct (n : Nat) : RelCT isa (Two (RoundAt n)) (roundTests n) (fun _ _ => True) := by
  unfold roundTests
  refine RelCT.seq (roundCompare_phase_ct n) (RelCT.seq (R := Two (RoundCoreAt n)) ?_ ?_)
  · apply two_ite (fun _ _ _ hs ht => by simp only [eval, hs.2, ht.2])
    · exact (roundAccept_ct n).mono (fun _ _ => two_mono (fun _ _ h => h.1.1)) (fun _ _ h => h)
    · exact (roundRemaining_ct n).mono (fun _ _ => two_mono (fun _ _ h => h.1.1)) (fun _ _ h => h)
  · exact two_taint [.edi] (roundCore_pins n) (by taint_decide)
end VG.Proof.Dsa.X86.Generation
