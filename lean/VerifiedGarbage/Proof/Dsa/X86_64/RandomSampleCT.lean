module
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSamplePublic

import VerifiedGarbage.Proof.Dsa.X86_64.RandomSampleLoopCT
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSample
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSampleLoopCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSample
import VerifiedGarbage.Proof.Dsa.X86_64.RandomFrame
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomFrame
import VerifiedGarbage.Proof.Bignum.CrtMath
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
import VerifiedGarbage.Proof.Bignum.X86_64.CrtGPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.Exp
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.Random
import VerifiedGarbage.Proof.Dsa.RandomEncoding
import VerifiedGarbage.Proof.Dsa.RandomTrace
import VerifiedGarbage.Proof.Dsa.X86_64.Arithmetic
import VerifiedGarbage.Proof.Dsa.X86_64.CopyMasked
import VerifiedGarbage.Proof.Dsa.X86_64.Failure
import VerifiedGarbage.Proof.Dsa.X86_64.Load
import VerifiedGarbage.Proof.Dsa.X86_64.Operands
import VerifiedGarbage.Proof.Dsa.X86_64.Prepare
import VerifiedGarbage.Proof.Dsa.X86_64.RandomBorrow
import VerifiedGarbage.Proof.Dsa.X86_64.RandomCT
import VerifiedGarbage.Proof.Dsa.X86_64.RandomCopy
import VerifiedGarbage.Proof.Dsa.X86_64.RandomCopyCT
import VerifiedGarbage.Proof.Dsa.X86_64.RandomCopyCandidate
import VerifiedGarbage.Proof.Dsa.X86_64.RandomCopyInit
import VerifiedGarbage.Proof.Dsa.X86_64.RandomCopyWhole
import VerifiedGarbage.Proof.Dsa.X86_64.RandomDraw
import VerifiedGarbage.Proof.Dsa.X86_64.RandomDrawCheckCT
import VerifiedGarbage.Proof.Dsa.X86_64.RandomDrawCopy
import VerifiedGarbage.Proof.Dsa.X86_64.RandomDrawFinishCT
import VerifiedGarbage.Proof.Dsa.X86_64.RandomDrawRange
import VerifiedGarbage.Proof.Dsa.X86_64.RandomFunctional
import VerifiedGarbage.Proof.Dsa.X86_64.RandomInRange
import VerifiedGarbage.Proof.Dsa.X86_64.RandomMemory
import VerifiedGarbage.Proof.Dsa.X86_64.RandomNonceEncoding
import VerifiedGarbage.Proof.Dsa.X86_64.RandomRange
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSampleLoop
import VerifiedGarbage.Proof.Dsa.X86_64.RandomScan
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceCount
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceRead
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceSetup
import VerifiedGarbage.Proof.Dsa.X86_64.SignificantLoop
import VerifiedGarbage.Proof.Dsa.Zero
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Poly1305.Limbs64
import VerifiedGarbage.Proof.RsaPss.Params
meta import VerifiedGarbage.Proof.Bignum.CrtMath
meta import VerifiedGarbage.Proof.Bignum.LazyMath
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
meta import VerifiedGarbage.Proof.Bignum.X86_64.Copy
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtGPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
meta import VerifiedGarbage.Proof.Bignum.X86_64.Csub
meta import VerifiedGarbage.Proof.Bignum.X86_64.Exp
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
meta import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
meta import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Bignum.X86_64.Valid
meta import VerifiedGarbage.Proof.Dsa.Arithmetic
meta import VerifiedGarbage.Proof.Dsa.Digest
meta import VerifiedGarbage.Proof.Dsa.Encoding
meta import VerifiedGarbage.Proof.Dsa.Random
meta import VerifiedGarbage.Proof.Dsa.RandomEncoding
meta import VerifiedGarbage.Proof.Dsa.RandomTrace
meta import VerifiedGarbage.Proof.Dsa.X86_64.Arithmetic
meta import VerifiedGarbage.Proof.Dsa.X86_64.CopyMasked
meta import VerifiedGarbage.Proof.Dsa.X86_64.Failure
meta import VerifiedGarbage.Proof.Dsa.X86_64.Load
meta import VerifiedGarbage.Proof.Dsa.X86_64.Operands
meta import VerifiedGarbage.Proof.Dsa.X86_64.Prepare
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomBorrow
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomCopy
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomCopyCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomCopyCandidate
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomCopyInit
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomCopyWhole
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomDraw
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomDrawCheckCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomDrawCopy
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomDrawFinishCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomDrawRange
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomFunctional
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomInRange
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomMemory
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomNonceEncoding
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomRange
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSampleLoop
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomScan
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceCount
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceRead
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceSetup
meta import VerifiedGarbage.Proof.Dsa.X86_64.SignificantLoop
meta import VerifiedGarbage.Proof.Dsa.Zero
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Poly1305.Limbs64
meta import VerifiedGarbage.Proof.RsaPss.Params

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
