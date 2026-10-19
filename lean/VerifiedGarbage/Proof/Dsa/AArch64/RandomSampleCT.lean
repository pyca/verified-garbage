module
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSamplePublic

import VerifiedGarbage.Proof.Dsa.AArch64.RandomSampleLoopCT
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSample
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSamplePublic
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSampleLoopCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSample
meta import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! The complete sampler's leakage is determined by its public decision trace. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64 VG.Impl.Bignum.AArch64

def RandomSamplePre (p : RandomSamplePublic) (s : State) : Prop :=
  p.draw.draws = 128 ∧ ∃ rand, ∃ hlen : rand.length = p.draw.randLen, ∃ m draws,
    RandomReady (p.draw.context rand hlen m) p.draw.used draws s ∧
    (Spec.Dsa.Random.sample (Spec.Dsa.decodeBE p.draw.qBytes) 128 (rand.drop p.draw.used)).trace = p.trace

private theorem init_ok {p : RandomSamplePublic} {s : State} (h : RandomSamplePre p s) :
    WP isa (.block ([movi .x0 128] ++ Random.store Random.oDraws .x0 ++
      [movi .x0 4] ++ Random.store Random.oStatus .x0)) s (RandomSampleTraceAt 128 p) := by
  obtain ⟨hn, rand, hlen, m, draws, hr, ht⟩ := h
  refine WP.mono (WP.keep [.x0, .x15] (Q := fun t =>
      t.mem = (s.mem.writeW (off p.draw.B Random.oDraws) (128 : BitVec 64)).writeW
        (off p.draw.B Random.oStatus) (4 : BitVec 64)) (by
      unfold Random.store
      brun [exec_addSp (show Random.oDraws < 4096 by decide),
        exec_addSp (show Random.oStatus < 4096 by decide), hr.sp, hr.scr.st (d := Random.oDraws) (by decide),
        hr.scr.st (d := Random.oStatus) (by decide)]
      rfl) rfl rfl rfl) fun t ⟨hm, hk⟩ => ?_
  obtain ⟨htr, hs⟩ := random_sample_init_ready hr hm hk
  refine ⟨hn, rand, hlen, m, ?_, hs, ?_⟩
  · rw [hn]; exact htr
  · rw [hn]; exact ht

theorem random_sample_ct : RelCT isa (Two RandomSamplePre) Random.sample (fun _ _ => True) := by
  unfold Random.sample
  refine RelCT.seq (two_piece (Ψ := RandomSampleTraceAt 128) [] ?_ (by taint_decide)
    (fun _ _ h => init_ok h)) ?_
  · intro _ _ _ _ _ _ h; cases h
  · refine RelCT.seq (random_sampleLoop_ct 128) ?_
    exact two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)

end VG.Proof.Dsa.AArch64
