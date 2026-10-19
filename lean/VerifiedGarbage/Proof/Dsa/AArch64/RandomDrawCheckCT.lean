module

public import VerifiedGarbage.Proof.Dsa.AArch64.RandomDrawPublic
import VerifiedGarbage.Proof.Dsa.AArch64.RandomCopyCT
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomRangeCT
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomDrawCheck
import VerifiedGarbage.Proof.Dsa.AArch64.RandomDrawCopy
import VerifiedGarbage.Proof.Dsa.AArch64.RandomMemory
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomDrawPublic
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomCopyCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomRangeCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomDrawCheck
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomDrawCopy
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomMemory
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! The copy-and-check prefix leaks only public addresses and widths. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

def RandomDrawPublic.range (p : RandomDrawPublic) : RandomRangePublic :=
  ⟨p.B, p.Q + BitVec.ofNat 64 (p.qBytes.length - p.width), p.qBytes.length, p.width⟩

def RandomDrawCheckMid (p : RandomDrawPublic) (s : State) : Prop :=
  RandomRangePre p.range s ∧ word s.mem p.B Random.oUsed = BitVec.ofNat 64 p.used

theorem random_draw_copy_ct : RelCT isa (Two RandomDrawFullPre) Random.copy (fun _ _ => True) := by
  refine two_map (fun p => (⟨p.B, p.R, p.used, p.qBytes.length, p.width⟩ : RandomCopyPublic)) ?_ random_copy_ct
  intro p s ⟨⟨rand, hlen, m, hr⟩, hfull⟩
  have hn := VG.Proof.Dsa.significant_fits p.qBytes
  have hq := p.qlen
  have hp := p.positive
  refine ⟨hr.scr, hr.sp, hr.rand, hr.usedWord, hr.qLen, hr.width, hp, by dsimp only [RandomDrawPublic.width]; omega, ?_, ?_⟩
  · have hh := hr.randSrc.rd p.used (by dsimp only [RandomDrawPublic.context]; rw [hlen]; dsimp only [RandomDrawPublic.width] at hfull; omega)
    exact hh
  · change InRegions s.wr (off p.B Random.oNonce + BitVec.ofNat 64 p.qBytes.length - BitVec.ofNat 64 p.width) 1
    unfold RandomDrawPublic.width
    rw [random_nonce_addr p.B hn]
    exact hr.scr.st1 (by dsimp only [Random.frameBytes, RandomDrawPublic.width]; omega)

private theorem copy_mid {p : RandomDrawPublic} {s : State} (h : RandomDrawFullPre p s) :
    WP isa Random.copy s (RandomDrawCheckMid p) := by
  obtain ⟨⟨rand, hlen, m, hr⟩, hfull⟩ := h
  have hn := VG.Proof.Dsa.significant_fits p.qBytes
  have hq := p.qlen
  refine WP.mono (random_copy_draw_ok hr.scr hr.sp hr.rand hr.usedWord hr.width hr.qLen hr.mask
    hr.randSrc hq p.positive (by dsimp only [RandomDrawPublic.context]; rw [hlen]; exact hfull)) fun t ⟨_, _, _, _, hf, hk⟩ => ?_
  dsimp only [RandomDrawPublic.context] at hf
  have hf' : Outside p.B 200 32 s.mem t.mem := hf.mono (by omega) (by omega)
  have hw (d : Nat) (hd : d + 8 ≤ 200) : word t.mem p.B d = word s.mem p.B d :=
    hf'.word (Or.inl hd) (by omega)
  exact ⟨⟨hr.scr.congr hk.wr, hk.sp.trans hr.sp,
    (hw _ (by decide)).trans hr.qLen, (hw _ (by decide)).trans hr.width,
    (hw _ (by decide)).trans hr.q⟩, (hw _ (by decide)).trans hr.usedWord⟩

private theorem used_range {p : RandomDrawPublic} {s : State} (h : RandomDrawCheckMid p s) :
    WP isa (.block (([.ldrSp .x0 Random.oUsed, .ldrSp .x4 Random.oWidth,
      .add .x .x0 .x0 .x4] : List Instr) ++ Random.store Random.oUsed .x0)) s
      (RandomRangePre p.range) := by
  obtain ⟨⟨hs, hsp, hl, hn, hq⟩, hu⟩ := h
  refine WP.mono (random_used_ok hs hsp hu hn) fun t ⟨hm, hk⟩ => ?_
  have hw (d : Nat) (hd : d + 8 ≤ 144 ∨ 152 ≤ d) (hb : d + 8 ≤ 2 ^ 64) :
      word t.mem p.B d = word s.mem p.B d := by
    rw [hm]
    exact (writeW_outside _ p.B _ (by decide)).word hd hb
  exact ⟨hs.congr hk.wr, hk.sp.trans hsp,
    (hw _ (by decide) (by decide)).trans hl,
    (hw _ (by decide) (by decide)).trans hn,
    (hw _ (by decide) (by decide)).trans hq⟩

theorem random_drawCheck_ct : RelCT isa (Two RandomDrawFullPre) randomDrawCheck (fun _ _ => True) := by
  unfold randomDrawCheck
  refine RelCT.seq (two_post random_draw_copy_ct (fun _ _ h => copy_mid h)) ?_
  refine RelCT.seq (two_piece (Ψ := fun p s => RandomRangePre p.range s) [] ?_ (by taint_decide)
    (fun _ _ h => used_range h)) ?_
  · intro _ _ _ _ _ _ h; cases h
  · exact two_map RandomDrawPublic.range (fun _ _ h => h) random_inRange_ct

end VG.Proof.Dsa.AArch64
