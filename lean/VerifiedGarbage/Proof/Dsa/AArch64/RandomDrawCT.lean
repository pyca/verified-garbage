module
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomDrawPublic
public import VerifiedGarbage.Spec.Dsa.Random

import VerifiedGarbage.Proof.Dsa.AArch64.RandomDrawCheckCT
import VerifiedGarbage.Proof.Dsa.AArch64.RandomDrawFinishCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomDrawCheckCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomDrawFinishCT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcAdd
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcColumns
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCorrect
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtLoop
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtRow
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtSpill
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcEnd
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcExtend
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLayout
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoad
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoop
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcSquare
import VerifiedGarbage.Proof.Bignum.AArch64.Bytes
import VerifiedGarbage.Proof.Bignum.AArch64.Copy
import VerifiedGarbage.Proof.Bignum.AArch64.CrtArith
import VerifiedGarbage.Proof.Bignum.AArch64.CrtBuild
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChk
import VerifiedGarbage.Proof.Bignum.AArch64.CrtExp
import VerifiedGarbage.Proof.Bignum.AArch64.CrtGPow
import VerifiedGarbage.Proof.Bignum.AArch64.CrtP
import VerifiedGarbage.Proof.Bignum.AArch64.CrtPow
import VerifiedGarbage.Proof.Bignum.AArch64.CrtSel
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
import VerifiedGarbage.Proof.Bignum.AArch64.Csub
import VerifiedGarbage.Proof.Bignum.AArch64.Double
import VerifiedGarbage.Proof.Bignum.AArch64.Mont
import VerifiedGarbage.Proof.Bignum.AArch64.PcCT
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
import VerifiedGarbage.Proof.Bignum.AArch64.PcVerified
import VerifiedGarbage.Proof.Bignum.AArch64.PdExp
import VerifiedGarbage.Proof.Bignum.AArch64.PdLoad
import VerifiedGarbage.Proof.Bignum.AArch64.PdRest
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCorrect
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtRows
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMath
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRaw
import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
import VerifiedGarbage.Proof.Bignum.AArch64.PubR2
import VerifiedGarbage.Proof.Bignum.AArch64.PubValid
import VerifiedGarbage.Proof.Bignum.AArch64.R2dQuot
import VerifiedGarbage.Proof.Bignum.AArch64.R2dRecip
import VerifiedGarbage.Proof.Bignum.AArch64.R2dSub
import VerifiedGarbage.Proof.Bignum.AArch64.Reduce
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Bignum.AArch64.Setup
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCall
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallMont
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuard
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuardCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightMont
import VerifiedGarbage.Proof.Bignum.AArch64.SquareFinish
import VerifiedGarbage.Proof.Bignum.AArch64.SquareGuard
import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
import VerifiedGarbage.Proof.Bignum.AArch64.Store
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Dsa.AArch64.Arithmetic
import VerifiedGarbage.Proof.Dsa.AArch64.CopyMasked
import VerifiedGarbage.Proof.Dsa.AArch64.EnterLeave
import VerifiedGarbage.Proof.Dsa.AArch64.Failure
import VerifiedGarbage.Proof.Dsa.AArch64.Load
import VerifiedGarbage.Proof.Dsa.AArch64.Masks
import VerifiedGarbage.Proof.Dsa.AArch64.Operands
import VerifiedGarbage.Proof.Dsa.AArch64.Prepare
import VerifiedGarbage.Proof.Dsa.AArch64.RandomBorrow
import VerifiedGarbage.Proof.Dsa.AArch64.RandomCT
import VerifiedGarbage.Proof.Dsa.AArch64.RandomCopy
import VerifiedGarbage.Proof.Dsa.AArch64.RandomCopyCT
import VerifiedGarbage.Proof.Dsa.AArch64.RandomCopyCandidate
import VerifiedGarbage.Proof.Dsa.AArch64.RandomCopyInit
import VerifiedGarbage.Proof.Dsa.AArch64.RandomCopyWhole
import VerifiedGarbage.Proof.Dsa.AArch64.RandomDraw
import VerifiedGarbage.Proof.Dsa.AArch64.RandomDrawCopy
import VerifiedGarbage.Proof.Dsa.AArch64.RandomDrawRange
import VerifiedGarbage.Proof.Dsa.AArch64.RandomFrame
import VerifiedGarbage.Proof.Dsa.AArch64.RandomInRange
import VerifiedGarbage.Proof.Dsa.AArch64.RandomMemory
import VerifiedGarbage.Proof.Dsa.AArch64.RandomRange
import VerifiedGarbage.Proof.Dsa.AArch64.RandomScan
import VerifiedGarbage.Proof.Dsa.AArch64.ReduceCount
import VerifiedGarbage.Proof.Dsa.AArch64.ReduceRead
import VerifiedGarbage.Proof.Dsa.AArch64.ReduceSetup
import VerifiedGarbage.Proof.Dsa.AArch64.Setup
import VerifiedGarbage.Proof.Dsa.AArch64.SignificantLoop
import VerifiedGarbage.Proof.Dsa.AArch64.Store
import VerifiedGarbage.Proof.Dsa.AArch64.StoreSuffix
import VerifiedGarbage.Proof.Dsa.AArch64.ZeroMask
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.RandomEncoding
import VerifiedGarbage.Proof.Dsa.Zero
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Poly1305.Limbs64
import VerifiedGarbage.Proof.RsaPss.Params
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcAdd
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcColumns
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCorrect
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtLoop
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtRow
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtSpill
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcEnd
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcExtend
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLayout
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoad
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoop
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcSquare
meta import VerifiedGarbage.Proof.Bignum.AArch64.Bytes
meta import VerifiedGarbage.Proof.Bignum.AArch64.Copy
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtArith
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtBuild
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtChk
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtExp
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtGPow
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtP
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtPow
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtSel
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
meta import VerifiedGarbage.Proof.Bignum.AArch64.Csub
meta import VerifiedGarbage.Proof.Bignum.AArch64.Double
meta import VerifiedGarbage.Proof.Bignum.AArch64.Mont
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcVerified
meta import VerifiedGarbage.Proof.Bignum.AArch64.PdExp
meta import VerifiedGarbage.Proof.Bignum.AArch64.PdLoad
meta import VerifiedGarbage.Proof.Bignum.AArch64.PdRest
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCorrect
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtRows
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMath
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRaw
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubR2
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubValid
meta import VerifiedGarbage.Proof.Bignum.AArch64.R2dQuot
meta import VerifiedGarbage.Proof.Bignum.AArch64.R2dRecip
meta import VerifiedGarbage.Proof.Bignum.AArch64.R2dSub
meta import VerifiedGarbage.Proof.Bignum.AArch64.Reduce
meta import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
meta import VerifiedGarbage.Proof.Bignum.AArch64.Row
meta import VerifiedGarbage.Proof.Bignum.AArch64.Setup
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCall
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallMont
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuard
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuardCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightMont
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareFinish
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareGuard
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
meta import VerifiedGarbage.Proof.Bignum.AArch64.Store
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Dsa.AArch64.Arithmetic
meta import VerifiedGarbage.Proof.Dsa.AArch64.CopyMasked
meta import VerifiedGarbage.Proof.Dsa.AArch64.EnterLeave
meta import VerifiedGarbage.Proof.Dsa.AArch64.Failure
meta import VerifiedGarbage.Proof.Dsa.AArch64.Load
meta import VerifiedGarbage.Proof.Dsa.AArch64.Masks
meta import VerifiedGarbage.Proof.Dsa.AArch64.Operands
meta import VerifiedGarbage.Proof.Dsa.AArch64.Prepare
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomBorrow
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomCopy
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomCopyCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomCopyCandidate
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomCopyInit
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomCopyWhole
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomDraw
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomDrawCopy
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomDrawRange
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomFrame
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomInRange
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomMemory
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomRange
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomScan
meta import VerifiedGarbage.Proof.Dsa.AArch64.ReduceCount
meta import VerifiedGarbage.Proof.Dsa.AArch64.ReduceRead
meta import VerifiedGarbage.Proof.Dsa.AArch64.ReduceSetup
meta import VerifiedGarbage.Proof.Dsa.AArch64.Setup
meta import VerifiedGarbage.Proof.Dsa.AArch64.SignificantLoop
meta import VerifiedGarbage.Proof.Dsa.AArch64.Store
meta import VerifiedGarbage.Proof.Dsa.AArch64.StoreSuffix
meta import VerifiedGarbage.Proof.Dsa.AArch64.ZeroMask
meta import VerifiedGarbage.Proof.Dsa.Arithmetic
meta import VerifiedGarbage.Proof.Dsa.Digest
meta import VerifiedGarbage.Proof.Dsa.Encoding
meta import VerifiedGarbage.Proof.Dsa.RandomEncoding
meta import VerifiedGarbage.Proof.Dsa.Zero
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Poly1305.Limbs64
meta import VerifiedGarbage.Proof.RsaPss.Params

/-! A draw leaks its public bounds and the declassified acceptance decision. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64 VG.Impl.Bignum.AArch64

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
  RandomDrawDecisionPre p s ∧ s.gpr .x3 = BitVec.ofNat 64 (if p.draw.randLen - p.draw.used < p.draw.width then 1 else 0)

private theorem head_ok {p : RandomDrawDecisionPublic} {s : State} (h : RandomDrawDecisionPre p s) :
    WP isa (.block [.ldrSp .x0 Random.oRandLen, .ldrSp .x4 Random.oUsed,
      .sub .x .x0 .x0 .x4, .ldrSp .x4 Random.oWidth, .subs .x .x3 .x0 .x4,
      movi .x0 0, movi .x4 1, .csel .x .x3 .x0 .x4]) s
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
    (h : RandomDrawHeadPost p s) (hc : isa.eval (.nonzero .x .x3) s = some false) :
    p.draw.used + p.draw.width ≤ p.draw.randLen := by
  by_contra hf
  have hshort : p.draw.randLen - p.draw.used < p.draw.width := by
    have := p.draw.usedBound
    omega
  simp [eval, State.read, h.2, hshort] at hc

def RandomDrawDecisionFull (p : RandomDrawDecisionPublic) (s : State) : Prop :=
  RandomDrawDecisionPre p s ∧ p.draw.used + p.draw.width ≤ p.draw.randLen

private theorem check_finish {p : RandomDrawDecisionPublic} {s : State} (h : RandomDrawDecisionFull p s) :
    WP isa randomDrawCheck s (RandomDrawFinishPre ⟨p.draw.B, p.draw.draws, p.accept⟩) := by
  obtain ⟨⟨rand, hlen, m, hr, ha⟩, hfull⟩ := h
  refine WP.mono (random_drawCheck_ok hr (by dsimp only [RandomDrawPublic.context]; rw [hlen]; exact hfull))
    fun t ⟨hs, hsp, hd, hz⟩ => ?_
  refine ⟨hs, hsp, hd, ?_, p.draw.drawsPos, p.draw.drawsBound⟩
  change t.gpr .x8 = BitVec.ofNat 64 (if p.accept then 1 else 0)
  have hz' : t.gpr .x8 = BitVec.ofNat 64 (if randomDrawAccept p.draw rand then 1 else 0) := by
    dsimp only [RandomDrawPublic.context] at hz
    let k := Spec.Dsa.Random.candidate (Spec.Dsa.decodeBE p.draw.qBytes)
      ((rand.drop p.draw.used).take p.draw.width)
    change t.gpr .x8 = BitVec.ofNat 64 (if 0 < k ∧ k < Spec.Dsa.decodeBE p.draw.qBytes then 1 else 0) at hz
    by_cases h : 0 < k ∧ k < Spec.Dsa.decodeBE p.draw.qBytes
    · have he : randomDrawAccept p.draw rand = true := decide_eq_true h
      rw [he]
      rw [ite_eq_left h] at hz
      exact hz
    · have he : randomDrawAccept p.draw rand = false := decide_eq_false h
      rw [he]
      rw [ite_eq_right h] at hz
      exact hz
  rw [ha hfull] at hz'
  exact hz'

private theorem full_ct : RelCT isa (Two RandomDrawDecisionFull)
    (.seq randomDrawCheck Random.drawFinish) (fun _ _ => True) := by
  refine RelCT.seq (two_post (two_map RandomDrawDecisionPublic.draw
    (fun _ _ h => ⟨h.1.drawPre, h.2⟩) random_drawCheck_ct) (fun _ _ h => check_finish h)) ?_
  exact two_map (fun p => (⟨p.draw.B, p.draw.draws, p.accept⟩ : RandomDrawFinishPublic))
    (fun _ _ h => h) random_drawFinish_ct

theorem random_draw_ct : RelCT isa (Two RandomDrawDecisionPre) Random.draw (fun _ _ => True) := by
  unfold Random.draw
  refine RelCT.seq (two_piece (Ψ := RandomDrawHeadPost) [] ?_ (by taint_decide)
    (fun _ _ h => head_ok h)) ?_
  · intro _ _ _ _ _ _ h; cases h
  · refine two_ite (fun p s t hs ht => by simp only [eval, State.read, hs.2, ht.2]) ?_ ?_
    · exact two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)
    · intro s t ts tt u v ⟨p, hs, ht, hsp⟩ es et
      have hp : Two RandomDrawDecisionFull s t :=
        ⟨p, ⟨hs.1.1, full_of_head hs.1 hs.2⟩, ⟨ht.1.1, full_of_head ht.1 ht.2⟩, hsp⟩
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

end VG.Proof.Dsa.AArch64
