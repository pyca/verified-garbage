module
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomDrawPublic
public import VerifiedGarbage.Spec.Dsa.Random
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel

import VerifiedGarbage.Proof.Dsa.X86_64.RandomDrawCheckCT
import VerifiedGarbage.Proof.Dsa.X86_64.RandomDrawFinishCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomDrawCheckCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomDrawFinishCT
import VerifiedGarbage.Proof.Framework.Omega
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
import VerifiedGarbage.Proof.Dsa.RandomEncoding
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
import VerifiedGarbage.Proof.Dsa.X86_64.RandomDrawCopy
import VerifiedGarbage.Proof.Dsa.X86_64.RandomDrawRange
import VerifiedGarbage.Proof.Dsa.X86_64.RandomFrame
import VerifiedGarbage.Proof.Dsa.X86_64.RandomInRange
import VerifiedGarbage.Proof.Dsa.X86_64.RandomMemory
import VerifiedGarbage.Proof.Dsa.X86_64.RandomRange
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
meta import VerifiedGarbage.Proof.Dsa.RandomEncoding
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
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomDrawCopy
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomDrawRange
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomFrame
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomInRange
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomMemory
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomRange
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

/-! A draw leaks its public bounds and the declassified acceptance decision. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

structure RandomDrawDecisionPublic where
  draw : RandomDrawPublic
  accept : Bool

def randomDrawAccept (p : RandomDrawPublic) (rand : List Byte) : Bool :=
  let k := Spec.Dsa.Random.candidate (Spec.Dsa.decodeBE p.qBytes) ((rand.drop p.used).take p.width)
  decide (0 < k ∧ k < Spec.Dsa.decodeBE p.qBytes)

def RandomDrawDecisionPre (p : RandomDrawDecisionPublic) (s : State) : Prop :=
  ∃ rand, ∃ hlen : rand.length = p.draw.randLen, ∃ m,
    RandomReady (p.draw.context rand hlen m) p.draw.used p.draw.draws s ∧
    (p.draw.used + p.draw.width ≤ p.draw.randLen → randomDrawAccept p.draw rand = p.accept)

theorem RandomDrawDecisionPre.drawPre {p : RandomDrawDecisionPublic} {s : State}
    (h : RandomDrawDecisionPre p s) : RandomDrawPre p.draw s := by
  obtain ⟨rand, hlen, m, hr, _⟩ := h
  exact ⟨rand, hlen, m, hr⟩

def RandomDrawHeadPost (p : RandomDrawDecisionPublic) (s : State) : Prop :=
  RandomDrawDecisionPre p s ∧ s.cf = some (decide (p.draw.randLen - p.draw.used < p.draw.width))

private theorem head_ok {p : RandomDrawDecisionPublic} {s : State} (h : RandomDrawDecisionPre p s) :
    WP isa (.block [.mov .rax (.mem (Random.sp Random.oRandLen)),
      .alu .sub .rax (.mem (Random.sp Random.oUsed)), .alu .cmp .rax (.mem (Random.sp Random.oWidth))]) s
      (RandomDrawHeadPost p) := by
  obtain ⟨rand, hlen, m, hr, ha⟩ := h
  have hrlen : word s.mem p.draw.B Random.oRandLen = BitVec.ofNat 64 p.draw.randLen := by
    simpa only [RandomDrawPublic.context, hlen] using hr.randLen
  have hw := VG.Proof.Dsa.significant_fits p.draw.qBytes
  have hq := p.draw.qlen
  refine WP.mono (random_drawHead_ok hr.scr hr.sp hrlen hr.usedWord hr.width p.draw.usedBound p.draw.randBound
    (by dsimp only [RandomDrawPublic.context]; omega)) fun t ⟨hc, hm, hk⟩ => ?_
  exact ⟨⟨rand, hlen, m, hr.congr hm hk, ha⟩, hc⟩

private theorem full_of_head {p : RandomDrawDecisionPublic} {s : State}
    (h : RandomDrawHeadPost p s) (hc : isa.eval .b s = some false) :
    p.draw.used + p.draw.width ≤ p.draw.randLen := by
  simp only [eval, h.2, Option.some.injEq, decide_eq_false_iff_not] at hc
  have := p.draw.usedBound
  omega

def RandomDrawDecisionFull (p : RandomDrawDecisionPublic) (s : State) : Prop :=
  RandomDrawDecisionPre p s ∧ p.draw.used + p.draw.width ≤ p.draw.randLen

private theorem check_finish {p : RandomDrawDecisionPublic} {s : State} (h : RandomDrawDecisionFull p s) :
    WP isa randomDrawCheck s (RandomDrawFinishPre ⟨p.draw.B, p.draw.draws, p.accept⟩) := by
  obtain ⟨⟨rand, hlen, m, hr, ha⟩, hfull⟩ := h
  refine WP.mono (random_drawCheck_ok hr (by dsimp only [RandomDrawPublic.context]; rw [hlen]; exact hfull))
    fun t ⟨hs, hsp, hd, hz⟩ => ?_
  refine ⟨hs, hsp, hd, ?_, p.draw.drawsPos, p.draw.drawsBound⟩
  change t.zf = some (!p.accept)
  change t.zf = some (!(randomDrawAccept p.draw rand)) at hz
  rw [ha hfull] at hz
  exact hz

private theorem full_ct : RelCT isa (Two RandomDrawDecisionFull)
    (.seq randomDrawCheck Random.drawFinish) (fun _ _ => True) := by
  refine RelCT.seq (two_post (two_map RandomDrawDecisionPublic.draw
    (fun _ _ h => ⟨h.1.drawPre, h.2⟩) random_drawCheck_ct) (fun _ _ h => check_finish h)) ?_
  exact two_map (fun p => (⟨p.draw.B, p.draw.draws, p.accept⟩ : RandomDrawFinishPublic))
    (fun _ _ h => h) random_drawFinish_ct

theorem random_draw_ct : RelCT isa (Two RandomDrawDecisionPre) Random.draw (fun _ _ => True) := by
  unfold Random.draw
  refine RelCT.seq (two_piece (Ψ := RandomDrawHeadPost) [.rsp] ?_ (by taint_decide)
    (fun _ _ h => head_ok h)) ?_
  · intro p s t hs ht r hr
    rw [List.mem_singleton] at hr
    subst r
    exact hs.drawPre.sp.trans ht.drawPre.sp.symm
  · refine two_ite (fun p s t hs ht => by simp only [eval, hs.2, ht.2]) ?_ ?_
    · apply two_taint [.rsp] ?_ (by taint_decide)
      intro p s t hs ht r hr
      rw [List.mem_singleton] at hr
      subst r
      exact hs.1.1.drawPre.sp.trans ht.1.1.drawPre.sp.symm
    · intro s t ts tt u v ⟨p, hs, ht⟩ es et
      have hp : Two RandomDrawDecisionFull s t :=
        ⟨p, ⟨hs.1.1, full_of_head hs.1 hs.2⟩, ht.1.1, full_of_head ht.1 ht.2⟩
      cases es with
      | seq sc sr => cases sr with
        | seq su sr => cases sr with
          | seq sk sf =>
            cases et with
            | seq tc tr => cases tr with
              | seq tu tr => cases tr with
                | seq tk tf =>
                  have hh := full_ct _ _ _ _ _ _ hp (.seq (.seq sc (.seq su sk)) sf)
                    (.seq (.seq tc (.seq tu tk)) tf)
                  simpa only [List.append_assoc] using hh

end VG.Proof.Dsa.X86_64
