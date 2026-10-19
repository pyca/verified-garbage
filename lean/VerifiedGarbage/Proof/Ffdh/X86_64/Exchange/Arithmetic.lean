module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.Data
public import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.R2
import VerifiedGarbage.Proof.Bignum.Octets

/-! # FFDH exchange on x86-64: the arithmetic stages -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Exchange

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def Entered (p : ExP) (xb : List Byte) (s : State) : Prop :=
  ∃ mi, Base p xb s ∧ SubCtx s p.B p.Z (inner p.w) p.w p.w mi ∧ XVals s p.B (inner p.w) p.w mi p.P

def Ready (p : ExP) (xb : List Byte) (s : State) : Prop :=
  ∃ mi, Base p xb s ∧ ModCtx s p.B p.Z (inner p.w) p.w mi p.P

def Value (p : ExP) (xb : List Byte) (s : State) : Prop :=
  Ready p xb s ∧ wv s.mem (off p.B (inner p.w)) (slot p.w aY) p.w = p.z xb

def Checked (p : ExP) (xb : List Byte) (s : State) : Prop :=
  (∃ mi, Base p xb s ∧ SubCtx s p.B p.Z (inner p.w) p.w p.w mi) ∧
    wv s.mem (off p.B (inner p.w)) (slot p.w aY) p.w = p.z xb ∧
    s.gpr .rax = bit (p.fl xb) ∧ word s.mem (off p.B (inner p.w)) (8 * sF) = bit (p.fl xb)

/-- Frames returned by the internal stages keep the saved ABI registers. -/
def StepPost (p : ExP) (s : State) (P : State → Prop) (t : State) : Prop :=
  P t ∧ InScr p.B p.Z s.mem t.mem ∧
    (∀ i < 6, word t.mem p.B (8 * i) = word s.mem p.B (8 * i)) ∧ Keep (.rdi :: mmRegs) s t

theorem setup_entered {p : ExP} {xb : List Byte} {s : State} (h : Base p xb s)
    (hdi : s.gpr .rdi = p.B) (hm : p.mv = true) :
    WP isa (seqs (([.block VG.Impl.Rsa.X86_64.head] : List (Prog isa)) ++ pSetup)) s
      (StepPost p s (Entered p xb)) := by
  obtain ⟨ho, _⟩ := valid_facts hm h.k1
  exact WP.mono (setup_ok (B := p.B) (Z := p.Z) (k := p.k) (dp := p.dp) (pb := p.pb) h.scr hdi h.k1 h.k2 h.hZ
    (h.hdr (sDom, p.dp) (by simp [ExP.headers])) (h.hdr (sK, BitVec.ofNat 64 p.k) (by simp [ExP.headers]))
    (h.dom.take p.k) h.plen ho) fun t ⟨mi, hc, hv, _, hf, k⟩ => by
      obtain ⟨hi, hh, hs⟩ := setup_frame h.k1 h.hZ hf
      exact ⟨⟨mi, h.keep hi k hh, hc, hv⟩, hi, hs, k⟩

theorem entered_ready (M : Mont) (R : R2Impl M) {p : ExP} {xb : List Byte} {s : State}
    (h : Entered p xb s) (hm : p.mv = true) :
    WP isa (.seq (.block r2Head) R.code) s (StepPost p s (Ready p xb)) := by
  obtain ⟨mi, hb, hc, hv⟩ := h
  exact WP.mono (r2_ctx M R hc hv hm hb.k1 hb.k2 hb.hZ)
    fun t ⟨hc', hf, k⟩ => by
      obtain ⟨hb, hi, hs⟩ := hb.child hc hf
        (fun r hr => by have := r2Ranges_le p.w r hr; omega) k
      exact ⟨⟨mi, hb, hc'⟩, hi, hs, k.mono (by decide)⟩

theorem ready_value (M : Mont) (E : CrtExpL M) {p : ExP} {xb : List Byte} {s : State}
    (h : Ready p xb s) :
    WP isa (seqs (pow M.mm E.code sY sK sX sXl)) s (StepPost p s (Value p xb)) := by
  obtain ⟨mi, hb, hc⟩ := h
  refine WP.mono (pow_ok M E hc (bp := sY) (bl := sK) (ep := sX) (el := sXl)
    (pb := p.yp) (pe := p.xp) (bb := p.yb) (eb := xb) (by decide) (by decide) (by decide) (by decide)
    (hb.hdr (sY, p.yp) (by simp [ExP.headers]))
    (by rw [hb.ylen]; exact hb.hdr (sK, BitVec.ofNat 64 p.k) (by simp [ExP.headers])) hb.y
    (by rw [hb.ylen]; exact Nat.le_trans (by decide) hb.k1) (by rw [hb.ylen])
    (hb.hdr (sX, p.xp) (by simp [ExP.headers]))
    (by rw [hb.xlen]; exact hb.hdr (sXl, BitVec.ofNat 64 p.xl) (by simp [ExP.headers])) hb.x
    (by rw [hb.xlen]; exact hb.xl1) (by rw [hb.xlen]; exact hb.xl2.trans hb.k2))
    fun t ⟨hc', hy, hf, k⟩ => ?_
  obtain ⟨hb', hi, hs⟩ := hb.child hc.sub hf (fun r hr => (powRanges_ok p.w r hr).2) k
  exact ⟨⟨⟨mi, hb', hc'⟩, hy⟩, hi, hs, k.mono (by decide)⟩

def rangeRanges (w : Nat) : List (Nat × Nat) := [(slot w aTmp, 8 * w), (8 * sF, 8)]

theorem rangeRanges_ok (w : Nat) : ∀ r ∈ rangeRanges w, 8 * 17 ≤ r.1 ∧ r.1 + r.2 ≤ slot w 8 := by
  have hT := slot_le (w := w) (show aTmp < 8 by decide)
  have hT0 := hdr_lt_slot w aTmp (show 31 < 32 by decide)
  have hF := hdr_lt_slot w 8 (show sF < 32 by decide)
  simp only [rangeRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl) <;> simp only <;> unfold sF sFn at * <;> omega

theorem value_checked {p : ExP} {xb : List Byte} {s : State} (h : Value p xb s) :
    WP isa (seqs (range aY)) s (StepPost p s (Checked p xb)) := by
  obtain ⟨⟨mi, hb, hc⟩, hy⟩ := h
  have hn := hc.sub.good.scr.nowrap
  have hYle := slot_le (w := p.w) (show aY < 8 by decide)
  have hw := hc.w2
  have hw' := hc.w28
  refine WP.mono (range_ok hc.sub.good (Nat.le_refl _) (by omega) (by omega)
    (show aY < 8 by decide) (by decide) hc.xv.one) fun t ⟨ha, hF, hf, k⟩ => ?_
  rw [hy, hc.xv.n] at ha
  obtain ⟨hb, hi, hs⟩ := hb.child hc.sub hf
    (fun r hr => by have := (rangeRanges_ok p.w r hr).2; omega) k
  have hc' := hc.sub.of_frm hf (rangeRanges_ok p.w) k.2.2 (k.gpr (by decide))
  have hy' : wv t.mem (off p.B (inner p.w)) (slot p.w aY) p.w = p.z xb := by
    rw [hf.wv_eq (fun r hr => ?_) (by omega), hy]
    have sTY := slot_sep (w := p.w) (show aTmp ≠ aY by decide)
    have hsY := hdr_lt_slot p.w aY (show sF < 32 by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simp only; omega
    · exact Or.inr hsY
  exact ⟨⟨⟨mi, hb, hc'⟩, hy', ha, hF.trans ha⟩, hi, hs, k.mono (by decide)⟩

end VG.Proof.Ffdh.X86_64.Exchange
