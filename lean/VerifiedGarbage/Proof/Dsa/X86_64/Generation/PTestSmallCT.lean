module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateWidthCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateWidthCT
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PAttempt
meta import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PAttempt

/-! # Width rejection has a fixed trace and does not enter primality testing -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum.X86_64
open VG.Impl.Dsa.X86_64.Generation

def PTestSmallBefore (p : CandidateWidthPublic) (s : State) : Prop :=
  CandidateWidthBefore p s ∧ p.value < 2 ^ (8 * p.len - 1)

theorem pTest_small_ct (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa) (len : Nat) :
    RelCT isa (Two PTestSmallBefore) (pTest mul round len) (fun _ _ => True) := by
  unfold pTest
  have guard : RelCT isa (Two PTestSmallBefore) (.block candidateWidth)
      (Two (fun (p : CandidateWidthPublic) s => s.gpr .rsp = p.F ∧ s.cf = some true)) := by
    refine two_post (candidateWidth_ct.mono (fun _ _ => two_mono fun _ _ h => h.1)
      (fun _ _ _ => True.intro)) ?_
    intro p s h
    exact WP.mono (candidateWidth_ready h.1) fun _ ht => ⟨ht.1.stack, by simp [ht.2, h.2]⟩
  refine RelCT.seq guard (two_ite (fun _ _ _ hs ht => by simp only [eval, hs.2, ht.2]) ?_ ?_)
  · exact two_taint [.rsp] (by
      intro p s t hs ht r hr
      simp only [List.mem_singleton] at hr; subst r
      exact hs.1.1.trans ht.1.1.symm) (by taint_decide)
  · apply RelCT.of_false
    rintro s t ⟨p, hs, _⟩
    simpa only [eval, hs.1.2, Bool.true_eq_false, Option.some.injEq] using hs.2

end VG.Proof.Dsa.X86_64.Generation
