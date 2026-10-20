module
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Flags
public import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl

import VerifiedGarbage.Proof.Ffdh.X86_64.R2
import VerifiedGarbage.Proof.Framework.Omega

/-! # FFDH private-key validation on x86-64: generator exponentiation -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckPrivate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def Ready (p : KpP) (xb : List Byte) (s : State) : Prop := ∃ mi,
  Base p xb s ∧ ModCtx s p.B p.Z (inner p.w) p.w mi p.P ∧ word s.mem p.B (8 * sG) = off p.dp p.k

def Value (p : KpP) (xb : List Byte) (s : State) : Prop :=
  Ready p xb s ∧ wv s.mem (off p.B (inner p.w)) (slot p.w aY) p.w = p.z xb

def Checked (p : KpP) (xb : List Byte) (s : State) : Prop := ∃ mi,
  Base p xb s ∧ SubCtx s p.B p.Z (inner p.w) p.w p.w mi ∧
    wv s.mem (off p.B (inner p.w)) (slot p.w aY) p.w = p.z xb ∧
    word s.mem (off p.B (inner p.w)) (8 * sF) = bit (p.fl xb)

theorem work_ready (M : Mont) (R : R2Impl M) {p : KpP} {xb : List Byte} {mi : BitVec 64} {s : State}
    (h : Work p xb mi s) (hd : s.gpr .rdi = off p.B (inner p.w)) (hm : p.mv = true) :
    WP isa (.seq (.block r2Head) R.code) s (StepPost p s (Ready p xb)) := by
  have hc := h.mem.ctx hd
  refine WP.mono (r2_ctx M R hc h.xv hm h.base.k1 h.base.k2 h.base.hZ) fun t ⟨hc', hf, k⟩ => ?_
  have hr : ∀ r ∈ r2Ranges p.w, r.1 + r.2 ≤ slot p.w 8 + tabBytes p.w 32 :=
    fun r hr => by have := r2Ranges_le p.w r hr; omega
  obtain ⟨hb, hi, hs⟩ := h.base.child hc hf hr k
  have hroom := room_k h.base.k1 h.base.hZ
  change inner p.w + slot p.w 8 + tabBytes p.w 32 ≤ p.Z at hroom
  obtain ⟨hh, _⟩ := child_frm hc hroom hf hr
  exact ⟨⟨mi, hb, hc', (hh _ (by decide)).trans h.hG⟩, hi, hs, k.mono (by decide)⟩

theorem ready_value (M : Mont) (E : CrtExpL M) {p : KpP} {xb : List Byte} {s : State}
    (h : Ready p xb s) :
    WP isa (seqs (pow M.mm E.code sG sK sX sXl)) s (StepPost p s (Value p xb)) := by
  obtain ⟨mi, hb, hc, hG⟩ := h
  have hgl : p.gb.length = p.k := by
    simp only [KpP.gb, List.length_take, List.length_drop, hb.doml]
    rcases hb.dl with hd | hd <;> rw [hd] <;> omega
  have hg : Src s p.B p.Z (off p.dp p.k) p.gb := (hb.dom.drop p.k).take p.k
  refine WP.mono (pow_ok M E hc (bp := sG) (bl := sK) (ep := sX) (el := sXl)
    (pb := off p.dp p.k) (pe := p.xp) (bb := p.gb) (eb := xb) (by decide) (by decide) (by decide) (by decide)
    hG (by rw [hgl]; exact hb.hdr (sK, BitVec.ofNat 64 p.k) (by simp [KpP.headers])) hg
    (by rw [hgl]; exact Nat.le_trans (by decide) hb.k1) (by rw [hgl])
    (hb.hdr (sX, p.xp) (by simp [KpP.headers]))
    (by rw [hb.xlen]; exact hb.hdr (sXl, BitVec.ofNat 64 p.xl) (by simp [KpP.headers])) hb.x
    (by rw [hb.xlen]; exact hb.xl1) (by rw [hb.xlen]; exact hb.xl2.trans hb.k2))
    fun t ⟨hc', hy, hf, k⟩ => ?_
  have hr := fun r hr => (powRanges_ok p.w r hr).2
  obtain ⟨hb', hi, hs⟩ := hb.child hc.sub hf hr k
  obtain ⟨hh, _⟩ := child_frm hc.sub hc.wide hf hr
  exact ⟨⟨⟨mi, hb', hc', (hh _ (by decide)).trans hG⟩, hy⟩, hi, hs, k.mono (by decide)⟩

def rangeRanges (w : Nat) : List (Nat × Nat) := [(slot w aTmp, 8 * w), (8 * sF, 8)]

theorem rangeRanges_ok (w : Nat) : ∀ r ∈ rangeRanges w, 8 * 17 ≤ r.1 ∧ r.1 + r.2 ≤ slot w 8 := by
  have hT := slot_le (w := w) (show aTmp < 8 by decide)
  have hT0 := hdr_lt_slot w aTmp (show 31 < 32 by decide)
  have hF := hdr_lt_slot w 8 (show sF < 32 by decide)
  simp only [rangeRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl) <;> simp only <;> unfold sF sFn at * <;> omega

theorem value_checked {p : KpP} {xb : List Byte} {s : State} (h : Value p xb s) :
    WP isa (seqs (range aY)) s (StepPost p s (Checked p xb)) := by
  obtain ⟨⟨mi, hb, hc, _⟩, hy⟩ := h
  have hn := hc.sub.good.scr.nowrap
  have hYle := slot_le (w := p.w) (show aY < 8 by decide)
  have hw := hc.w2
  have hw' := hc.w28
  refine WP.mono (range_ok hc.sub.good (Nat.le_refl _) (by omega) (by omega)
    (show aY < 8 by decide) (by decide) hc.xv.one) fun t ⟨ha, hF, hf, k⟩ => ?_
  rw [hy, hc.xv.n] at ha
  obtain ⟨hb', hi, hs⟩ := hb.child hc.sub hf (fun r hr => by have := (rangeRanges_ok p.w r hr).2; omega) k
  have hc' := hc.sub.of_frm hf (rangeRanges_ok p.w) k.2.2 (k.gpr (by decide))
  have hy' : wv t.mem (off p.B (inner p.w)) (slot p.w aY) p.w = p.z xb := by
    rw [hf.wv_eq (fun r hr => ?_) (by omega), hy]
    have sTY := slot_sep (w := p.w) (show aTmp ≠ aY by decide)
    have hsY := hdr_lt_slot p.w aY (show sF < 32 by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simp only; omega
    · exact Or.inr hsY
  exact ⟨⟨mi, hb', hc', hy', hF.trans ha⟩, hi, hs, k.mono (by decide)⟩

end VG.Proof.Ffdh.X86_64.CheckPrivate
