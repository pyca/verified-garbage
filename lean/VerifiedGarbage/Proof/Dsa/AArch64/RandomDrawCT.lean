module
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomDrawPublic
public import VerifiedGarbage.Spec.Dsa.Random

import VerifiedGarbage.Proof.Dsa.AArch64.RandomDrawCheckCT
import VerifiedGarbage.Proof.Dsa.AArch64.RandomDrawFinishCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomDrawPublic
meta import VerifiedGarbage.Spec.Dsa.Random
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomDrawCheckCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomDrawFinishCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

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
