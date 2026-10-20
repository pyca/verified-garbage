module
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.StagesCT

import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.OddCT
import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Range
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Loads
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Work
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.StagesCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.OddCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Range
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Loads
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Work
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # FFDH domain validation on x86-64: subgroup range in constant time -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def QInner (p : CdP) (s : State) : Prop := Inner p s ∧ p.dl = 3 * p.k

def QChecked (p : CdP) (s : State) : Prop := QInner p s ∧ s.zf = some (!decide p.qr)

theorem qinner_load (p : CdP) (s : State) (h : QInner p s) : LPre aXm sQ sK p.ql s := by
  obtain ⟨⟨mi, hw, hd, _⟩, hq⟩ := h
  have hb := hw.base
  have hk := hb.k1
  have hk' := hb.k2
  have hl := hb.qlen hq
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CdP.w; omega
  exact ⟨mi, p.qb, hw.mem.ctx hd, show 2 ≤ p.w by omega, Nat.le_refl _, show p.w < 2 ^ 30 by omega,
    by decide, by decide, by decide, hw.q,
    by rw [hl]; exact hb.hdr (sK, BitVec.ofNat 64 p.k) (by simp [CdP.headers]),
    hl, (hb.dom.drop (2 * p.k)).take p.k, by rw [hl]; omega,
    by rw [hl]; omega, by rw [hl]⟩

private theorem qinner_loaded (p : CdP) (s : State) (h : QInner p s) :
    WP isa (seqs (VG.Impl.Rsa.X86_64.Crt.loadArr aXm sQ sK)) s (QInner p) := by
  obtain ⟨⟨mi, hw, hd, hm⟩, hq⟩ := h
  exact WP.mono (load_order hw hd hq) fun _ ⟨⟨hw', hd', _⟩, _⟩ => ⟨⟨mi, hw', hd', hm⟩, hq⟩

private theorem qinner_ranged (p : CdP) (s : State) (h : QInner p s) :
    WP isa (seqs (range aXm)) s (QInner p) := by
  obtain ⟨⟨mi, hw, hd, hm⟩, hq⟩ := h
  exact WP.mono (component_range hw hd rfl) fun _ ⟨⟨hw', hd', _⟩, _⟩ => ⟨⟨mi, hw', hd', hm⟩, hq⟩

private theorem qinner_odd (p : CdP) (s : State) (h : QInner p s) :
    WP isa (seqs (isOdd aXm)) s (QInner p) := by
  obtain ⟨⟨mi, hw, hd, hm⟩, hq⟩ := h
  have hk := hw.base.k1
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CdP.w; omega
  exact WP.mono (isOdd_ok (hw.mem.ctx hd).good (Nat.le_refl _) (by omega) (show aXm < 8 by decide))
    fun _ ⟨_, hmem, k⟩ => ⟨⟨mi, hw.keep hmem k, (k.gpr (by decide)).trans hd, hm⟩, hq⟩

private theorem qinner_checked (p : CdP) (s : State) (h : QInner p s) :
    WP isa (seqs VG.Impl.Ffdh.X86_64.Domain.CheckDomain.qRange) s (QChecked p) := by
  obtain ⟨⟨mi, hw, hd, hm⟩, hq⟩ := h
  exact WP.mono (order_range hw hd hq) fun _ ⟨⟨hw', hd', hz⟩, _⟩ => ⟨⟨⟨mi, hw', hd', hm⟩, hq⟩, hz⟩

theorem qrange_ct : RelCT isa (Two QInner)
    (seqs VG.Impl.Ffdh.X86_64.Domain.CheckDomain.qRange) (Two QChecked) := by
  refine two_post ?_ qinner_checked
  unfold VG.Impl.Ffdh.X86_64.Domain.CheckDomain.qRange
  simp only [List.append_assoc]
  refine RelCT.seqs_append (by simp [VG.Impl.Rsa.X86_64.Crt.loadArr]) (by simp [range, gt1, ltArr, cmpArr])
    (RelCT.seq (R := Two QInner)
      (two_post (two_map CdP.ql qinner_load (loadArr_ct (by decide) (by taint_decide) (by taint_decide))) qinner_loaded) ?_)
  refine RelCT.seqs_append (by simp [range, gt1, ltArr, cmpArr]) (by simp [isOdd])
    (RelCT.seq (R := Two QInner)
      (two_post (two_map CdP.ws (fun p s h => inner_good p s h.1)
        (range_ct (a := aXm) (by decide) (by decide) (by taint_decide) (by taint_decide) (by taint_decide))) qinner_ranged) ?_)
  refine RelCT.seqs_append (by simp [isOdd]) (by simp)
    (RelCT.seq (R := Two QInner)
      (two_post (two_map CdP.ws (fun p s h => inner_good p s h.1) odd_ct) qinner_odd) ?_)
  exact two_taint [.rdi] (pins_rdiB (fun p => off p.B (inner p.w))
    fun _ _ ⟨⟨_, _, hd, _⟩, _⟩ => hd) (by taint_decide)

end VG.Proof.Ffdh.X86_64.CheckDomain
