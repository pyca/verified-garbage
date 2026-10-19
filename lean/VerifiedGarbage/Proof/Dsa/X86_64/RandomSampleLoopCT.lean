module

public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSampleStep
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSampleLoop
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSampleStep
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSampleLoop
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! The sampling loop reveals only the specified sequence of draw decisions. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

def randomSampleBody : Prog isa :=
  .seq Random.draw (.block [.mov .rax (.mem (Random.sp Random.oStatus)), .alu .cmp .rax (.imm 4)])

def RandomSampleTestPost (p : RandomSamplePublic) (s : State) : Prop :=
  RandomSampleStepPost p s ∧ s.zf = some (BitVec.ofNat 64 (randomSampleStepStatus p) == 4)

private theorem step_ct : RelCT isa (Two RandomSampleTracePre) randomSampleBody (fun _ _ => True) := by
  unfold randomSampleBody
  refine RelCT.seq (two_post (two_map (fun p => (⟨p.draw, p.accept⟩ : RandomDrawDecisionPublic))
    (fun _ _ h => h.decision) random_draw_ct) (fun _ _ h => random_sample_step h)) ?_
  apply two_taint [.rsp] ?_ (by taint_decide)
  intro p s t hs ht r hr
  rw [List.mem_singleton] at hr
  subst r
  exact hs.2.1.trans ht.2.1.symm

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
    RelCT isa (Two (RandomSampleTraceAt n)) (.loop randomSampleBody .e)
      (Two fun (B : Addr) s => s.gpr .rsp = B) := by
  refine RelCT.loop (M := isa) (fun n => Two (RandomSampleTraceAt n)) ?_ n
  intro fuel
  have hc : RelCT isa (Two (RandomSampleTraceAt fuel)) randomSampleBody
      (Two fun p s => p.draw.draws = fuel ∧ RandomSampleTestPost p s) := by
    refine two_post (step_ct.mono (fun _ _ h => two_mono (fun _ _ h => h.2) h) (fun _ _ _ => trivial)) ?_
    intro p s ⟨hn, hs⟩
    exact WP.mono (step_ok hs) fun _ ht => ⟨hn, ht⟩
  refine hc.mono (fun _ _ h => h) ?_
  intro s t ⟨p, ⟨hn, hs⟩, ⟨_, ht⟩⟩
  have he : isa.eval .e s = isa.eval .e t := by simp only [eval, hs.2, ht.2]
  refine ⟨he, fun _ => ⟨p.draw.B, hs.1.2.1, ht.1.2.1⟩, ?_⟩
  intro hcontinue
  have hfour : randomSampleStepStatus p = 4 := by
    simp only [eval, hs.2, Option.some.injEq, beq_iff_eq] at hcontinue
    have hn' := congrArg BitVec.toNat hcontinue
    have hb := status_bound p
    change randomSampleStepStatus p % 2 ^ 64 = 4 at hn'
    omega
  obtain ⟨hfull, hf, ha⟩ := random_sample_status_four hfour
  refine ⟨p.draw.draws - 1, by omega, p.next hfull hf, ?_, ?_⟩
  · exact ⟨rfl, hs.1.2.2.2 hfull hf ha⟩
  · exact ⟨rfl, ht.1.2.2.2 hfull hf ha⟩

end VG.Proof.Dsa.X86_64
