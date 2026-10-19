module
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSamplePublic

import VerifiedGarbage.Proof.Dsa.X86_64.RandomSampleLoopCT
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSample
import VerifiedGarbage.Proof.Dsa.X86_64.RandomFrame
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSamplePublic
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSampleLoopCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSample
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomFrame
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! The complete sampler's leakage is determined by its public decision trace. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

def RandomSamplePre (p : RandomSamplePublic) (s : State) : Prop :=
  p.draw.draws = 128 ∧ ∃ rand, ∃ hlen : rand.length = p.draw.randLen, ∃ m draws,
    RandomReady (p.draw.context rand hlen m) p.draw.used draws s ∧
    (Spec.Dsa.Random.sample (Spec.Dsa.decodeBE p.draw.qBytes) 128 (rand.drop p.draw.used)).trace = p.trace

private theorem init_ok {p : RandomSamplePublic} {s : State} (h : RandomSamplePre p s) :
    WP isa (.block [.mov .rax (.imm 128), .store (Random.sp Random.oDraws) .rax,
      .mov .rax (.imm 4), .store (Random.sp Random.oStatus) .rax]) s (RandomSampleTraceAt 128 p) := by
  obtain ⟨hn, rand, hlen, m, draws, hr, ht⟩ := h
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
      t.mem = (s.mem.writeW (off p.draw.B Random.oDraws) (128 : BitVec 64)).writeW
        (off p.draw.B Random.oStatus) (4 : BitVec 64)) (by
      xrun [random_ea_sp, hr.sp, hr.scr.st (d := Random.oDraws) (by decide),
        hr.scr.st (d := Random.oStatus) (by decide)]
      rfl) rfl) fun t ⟨hm, hk⟩ => ?_
  obtain ⟨htr, hs⟩ := random_sample_init_ready hr hm hk
  refine ⟨hn, rand, hlen, m, ?_, hs, ?_⟩
  · rw [hn]; exact htr
  · rw [hn]; exact ht

theorem random_sample_ct : RelCT isa (Two RandomSamplePre) Random.sample (fun _ _ => True) := by
  unfold Random.sample
  refine RelCT.seq (two_piece (Ψ := RandomSampleTraceAt 128) [.rsp] ?_ (by taint_decide)
    (fun _ _ h => init_ok h)) ?_
  · intro p s t hs ht r hr
    rw [List.mem_singleton] at hr
    subst r
    obtain ⟨_, _, _, _, _, hs, _⟩ := hs
    obtain ⟨_, _, _, _, _, ht, _⟩ := ht
    exact hs.sp.trans ht.sp.symm
  · refine RelCT.seq (random_sampleLoop_ct 128) ?_
    apply two_taint [.rsp] ?_ (by taint_decide)
    intro B s t hs ht r hr
    rw [List.mem_singleton] at hr
    subst r
    exact hs.trans ht.symm

end VG.Proof.Dsa.X86_64
