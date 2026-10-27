module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateWidthCT
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PAttempt
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateWidthCT
meta import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PAttempt
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! # Width rejection has a fixed trace and does not enter primality testing -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.AArch64.Generation

def PTestSmallBefore (p : CandidateWidthPublic) (s : State) : Prop :=
  CandidateWidthBefore p s ∧ p.value < 2 ^ (8 * p.len - 1)

theorem pTest_small_ct (prime : Nat → Prog isa) (len : Nat) :
    RelCT isa (Two PTestSmallBefore) (pTest prime len) (fun _ _ => True) := by
  unfold pTest
  have guard : RelCT isa (Two PTestSmallBefore) (.block candidateWidth)
      (Two (fun (p : CandidateWidthPublic) s => s.sp = p.F ∧ eval (.zero .x .x3) s = some true)) := by
    refine two_post (candidateWidth_ct.mono (fun _ _ => two_mono fun _ _ h => h.1)
      (fun _ _ _ => True.intro)) ?_
    intro p s h
    exact WP.mono (candidateWidth_ready h.1) fun _ ht => ⟨ht.1.stack, by simpa only [decide_eq_true h.2] using ht.2⟩
  refine RelCT.seq guard (two_ite (fun _ _ _ hs ht => hs.2.trans ht.2.symm) ?_ ?_)
  · exact two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)
  · apply RelCT.of_false
    rintro s t ⟨p, hs, _, _⟩
    cases Option.some.inj (hs.1.2.symm.trans hs.2)

end VG.Proof.Dsa.AArch64.Generation
