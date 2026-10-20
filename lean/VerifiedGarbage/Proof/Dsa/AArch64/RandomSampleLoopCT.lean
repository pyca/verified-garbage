module

public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSampleStep
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSampleLoop
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSampleStep
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSampleLoop
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! The sampling loop reveals only the specified sequence of draw decisions. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

def randomSampleBody : Prog isa :=
  .seq Random.draw (.block (Random.statusTest 4))

def RandomSampleTestPost (p : RandomSamplePublic) (s : State) : Prop :=
  RandomSampleStepPost p s ∧ (s.gpr .x4 == 0#64) = (BitVec.ofNat 64 (randomSampleStepStatus p) == 4)

private theorem step_ct : RelCT isa (Two RandomSampleTracePre) randomSampleBody (fun _ _ => True) := by
  unfold randomSampleBody
  refine RelCT.seq (two_post (two_map (fun p => (⟨p.draw, p.accept⟩ : RandomDrawDecisionPublic))
    (fun _ _ h => h.decision) random_draw_ct) (fun _ _ h => random_sample_step h)) ?_
  exact two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)

private theorem step_ok {p : RandomSamplePublic} {s : State} (h : RandomSampleTracePre p s) :
    WP isa randomSampleBody s (RandomSampleTestPost p) := by
  refine WP.seq (WP.mono (random_sample_step h) fun t ht => ?_)
  exact WP.mono (random_statusTest_ok ht.1 ht.2.1 ht.2.2.1)
    (fun _ ⟨hz, hm, hk⟩ => ⟨ht.congr hm hk, hz⟩)

private theorem status_bound (p : RandomSamplePublic) : randomSampleStepStatus p ≤ 4 := by
  unfold randomSampleStepStatus
  split
  · split
    · decide
    · split <;> decide
  · decide

def RandomSampleTraceAt (n : Nat) (p : RandomSamplePublic) (s : State) : Prop :=
  p.draw.draws = n ∧ RandomSampleTracePre p s

theorem random_sampleLoop_ct (n : Nat) :
    RelCT isa (Two (RandomSampleTraceAt n)) (.loop randomSampleBody (.zero .x .x4))
      (Two fun (B : Addr) s => s.sp = B) := by
  refine RelCT.loop (M := isa) (fun n => Two (RandomSampleTraceAt n)) ?_ n
  intro fuel
  have hc : RelCT isa (Two (RandomSampleTraceAt fuel)) randomSampleBody
      (Two fun p s => p.draw.draws = fuel ∧ RandomSampleTestPost p s) := by
    refine two_post (step_ct.mono (fun _ _ h => two_mono (fun _ _ h => h.2) h) (fun _ _ _ => trivial)) ?_
    intro p s ⟨hn, hs⟩
    exact WP.mono (step_ok hs) fun _ ht => ⟨hn, ht⟩
  refine hc.mono (fun _ _ h => h) ?_
  intro s t ⟨p, ⟨hn, hs⟩, ⟨_, ht⟩, hsp⟩
  have he : isa.eval (.zero .x .x4) s = isa.eval (.zero .x .x4) t := by
    change some (s.gpr .x4 == 0#64) = some (t.gpr .x4 == 0#64)
    rw [hs.2, ht.2]
  refine ⟨he, fun _ => ⟨p.draw.B, hs.1.2.1, ht.1.2.1, hsp⟩, ?_⟩
  intro hcontinue
  have hfour : randomSampleStepStatus p = 4 := by
    change some (s.gpr .x4 == 0#64) = some true at hcontinue
    rw [hs.2] at hcontinue
    simp only [Option.some.injEq, beq_iff_eq] at hcontinue
    have hn' := congrArg BitVec.toNat hcontinue
    have hb := status_bound p
    change randomSampleStepStatus p % 2 ^ 64 = 4 at hn'
    omega
  obtain ⟨hfull, hf, ha⟩ := random_sample_status_four hfour
  refine ⟨p.draw.draws - 1, by omega, p.next hfull hf, ?_, ?_, hsp⟩
  · exact ⟨rfl, hs.1.2.2.2 hfull hf ha⟩
  · exact ⟨rfl, ht.1.2.2.2 hfull hf ha⟩

end VG.Proof.Dsa.AArch64
