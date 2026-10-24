module

import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
public import VerifiedGarbage.Impl.Dsa.X86_64.PublicPower
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
import VerifiedGarbage.Proof.Dsa.X86_64.PublicWindow
import VerifiedGarbage.Proof.Dsa.X86_64.PublicSquares
import VerifiedGarbage.Proof.Dsa.X86_64.PublicSelect
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
meta import VerifiedGarbage.Impl.Dsa.X86_64.PublicPower
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
meta import VerifiedGarbage.Proof.Dsa.X86_64.PublicWindow
meta import VerifiedGarbage.Proof.Dsa.X86_64.PublicSelect
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Dsa.X86_64.PublicSquares

/-! # Public window addresses and branches depend only on the exponent -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.PublicPower
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64.PublicPower

/-- The digit, unlike the table values, is shared by both executions. -/
def SelectPre (p : XPub × Nat) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (X Xc : Nat), CExpCtx s (off p.1.B p.1.o) p.1.wx minv X Xc ∧
    2 ≤ p.1.wx ∧ p.1.wx < 2 ^ 30 ∧ p.2 < 16 ∧
    word s.mem (off p.1.B p.1.o) (8 * Crt.sTab) = off (off p.1.B p.1.o) (slot p.1.wx 8) ∧
    word s.mem (off p.1.B p.1.o) (8 * Crt.sNib) = BitVec.ofNat 64 p.2

def SelectRegs (p : XPub × Nat) (s : State) : Prop :=
  s.gpr .r12 = BitVec.ofNat 64 p.1.wx ∧
  s.gpr .rsi = off (off p.1.B p.1.o) (slot p.1.wx (8 + p.2)) ∧
  s.gpr .rbx = off (off p.1.B p.1.o) (slot p.1.wx Crt.aT)

theorem select_ct : RelCT isa (Two SelectPre) select (fun _ _ => True) := by
  unfold select
  refine RelCT.seq (two_piece (Ψ := SelectRegs) [.rdi]
    (pins_rdi (fun p : XPub × Nat => off p.1.B p.1.o) (fun _ _ ⟨_, _, _, hc, _⟩ => hc.good.rdi))
    (by taint_decide) (fun p s ⟨_, _, _, hc, _, _, _, ht, hn⟩ =>
      WP.mono (selectHead_ok hc ht hn) (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩))) ?_
  exact two_taint [.r12, .rsi, .rbx] (pins_of
    (fun p r => if r = .r12 then BitVec.ofNat 64 p.1.wx else
      if r = .rsi then off (off p.1.B p.1.o) (slot p.1.wx (8 + p.2)) else
        off (off p.1.B p.1.o) (slot p.1.wx Crt.aT)) (by
      intro p s h r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h.1
      · exact h.2.1
      · exact h.2.2)) (by taint_decide)

theorem applyWindow_ct (M : Mont) : RelCT isa (Two SelectPre) (applyWindow M.mm) (fun _ _ => True) := by
  unfold applyWindow
  refine RelCT.seq (two_piece (Ψ := fun p s => SelectPre p s ∧ s.zf = some (decide (p.2 = 0))) [.rdi]
    (pins_rdi (fun p : XPub × Nat => off p.1.B p.1.o) (fun _ _ ⟨_, _, _, hc, _⟩ => hc.good.rdi))
    (by taint_decide) ?_) ?_
  · intro p s ⟨minv, X, Xc, hc, hw, hw', hv, ht, hn⟩
    refine WP.mono (test_ok hc hv hn) fun t ⟨hm, hz, hk⟩ => ?_
    exact ⟨⟨minv, X, Xc, hc.of_win (hm ▸ Frm.refl _ _ _) hk.2.2 (hk.gpr (by decide)),
      hw, hw', hv, hm ▸ ht, hm ▸ hn⟩, hz⟩
  · apply RelCT.ite
    · rintro s t ⟨p, hs, ht⟩
      change s.zf = t.zf
      rw [hs.2, ht.2]
    · exact (two_taint (Φ := fun (_ : Unit) (_ : State) => True) [] (by intro p s t hs ht r hr; cases hr) (by taint_decide)).mono
        (fun _ _ _ => ⟨(), trivial, trivial⟩) (fun _ _ _ => trivial)
    · refine (RelCT.seq (two_post (Ψ := fun p s => GoodW p.1.ws s) select_ct ?_)
        (two_map (fun p : XPub × Nat => p.1.ws) (fun _ _ h => h)
          (M.ct (o := aY) (a := aY) (b := Crt.aT) (by unfold MmUse; decide)))).mono
        (fun _ _ ⟨⟨p, hs, ht⟩, _⟩ => ⟨p, hs.1, ht.1⟩) (fun _ _ _ => trivial)
      intro p s ⟨minv, X, Xc, hc, hw, hw', hv, ht, hn⟩
      exact WP.mono (select_ok hc hw hw' hv ht hn) (fun _ h => ⟨minv, h.1.good, Nat.le_refl _⟩)

/-- A window's input pins the shifted public exponent byte. -/
def WindowPre (bd : Nat → Nat → Nat) (p : XPub × Nat) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (X Xc : Nat), CExpCtx s (off p.1.B p.1.o) p.1.wx minv X Xc ∧
    CTab s.mem (off p.1.B p.1.o) p.1.wx X False 0 ∧
    wv s.mem (off p.1.B p.1.o) (slot p.1.wx aY) p.1.wx < bd X (2 ^ (64 * p.1.wx)) ∧
    word s.mem (off p.1.B p.1.o) (8 * Crt.sV) = BitVec.ofNat 64 p.2 ∧
    p.2 < 2 ^ 56 ∧ 2 ≤ p.1.wx ∧ p.1.wx < 2 ^ 30 ∧ Nat.Coprime (2 ^ (64 * p.1.wx)) X

theorem square_post (Sq : MontS) {p : XPub × Nat} {s : State} (h : WindowPre Sq.bd p s) :
    WP isa Sq.mm s (WindowPre Sq.bd p) := by
  obtain ⟨minv, X, Xc, hc, ht, hy, hv, hv', hw, hw', hR⟩ := h
  exact WP.mono (crtSqS_ok Sq (Q := False) (x := 0) (E := 0) hc hw hw' hR hy False.elim)
    fun t ⟨hc', hy', _, hh, hf, _⟩ => ⟨minv, X, Xc, hc', ht.of_win hf hc.scrT.nowrap, hy',
      (hh _ (by decide)).trans hv, hv', hw, hw', hR⟩

theorem mid_post {bd : Nat → Nat → Nat} {p : XPub × Nat} {s : State} (h : WindowPre bd p s) :
    WP isa (.block [.mov .rdx (.mem (hdr Crt.sV)), .mov .rax (.reg .rdx), .alu .add .rax (.reg .rax),
      .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
      .store (hdr Crt.sV) .rax, .shift .shr .rdx 4, .alu .and .rdx (.imm 15),
      .store (hdr Crt.sNib) .rdx]) s (SelectPre (p.1, p.2 / 16 % 16)) := by
  obtain ⟨minv, X, Xc, hc, ht, _, hv, hv', hw, hw', _⟩ := h
  refine WP.mono (winMid_ok hc hv (by omega)) fun t ⟨hm, hk⟩ => ?_
  have hf : Frm (off p.1.B p.1.o) (crtWinRanges p.1.wx) s.mem t.mem := by
    rw [hm]
    exact (Frm.of_outside (writeW_outside _ _ _ (d := 8 * Crt.sV) (by decide)) (by simp [crtWinRanges])).trans
      (Frm.of_outside (writeW_outside _ _ _ (d := 8 * Crt.sNib) (by decide)) (by simp [crtWinRanges]))
  exact ⟨minv, X, Xc, hc.of_win hf hk.2.2 (hk.gpr (by decide)), hw, hw', Nat.mod_lt _ (by decide),
    (ht.of_win hf hc.scrT.nowrap).tab, by rw [hm, word_writeW_self]⟩

private theorem count_window {p : XPub × Nat} {s t : State} {v : Nat} {bd : Nat → Nat → Nat}
    (h : WindowPre bd p s)
    (hm : t.mem = s.mem.writeW (off (off p.1.B p.1.o) (8 * Crt.sNib)) (BitVec.ofNat 64 v))
    (hk : Keep [.rax] s t) : WindowPre bd p t := by
  obtain ⟨mi, X, Xc, hc, ht, hy, hv, hv', hw, hw', hR⟩ := h
  obtain ⟨hc', _, hy', hh, hf⟩ := squareCounter_change hc hm hk
  exact ⟨mi, X, Xc, hc', ht.of_win hf hc.scrT.nowrap, hy' ▸ hy,
    (hh _ (by decide) (by decide)).trans hv, hv', hw, hw', hR⟩

private def CountPre (bd : Nat → Nat → Nat) (p : (XPub × Nat) × Nat) (s : State) : Prop :=
  WindowPre bd p.1 s ∧ word s.mem (off p.1.1.B p.1.1.o) (8 * Crt.sNib) = BitVec.ofNat 64 p.2

private theorem square_count_post (Sq : MontS) {p : (XPub × Nat) × Nat} {s : State}
    (h : CountPre Sq.bd p s) : WP isa Sq.mm s (CountPre Sq.bd p) := by
  obtain ⟨⟨mi, X, Xc, hc, ht, hy, hv, hv', hw, hw', hR⟩, hn⟩ := h
  exact WP.mono (crtSqS_ok Sq (Q := False) (x := 0) (E := 0) hc hw hw' hR hy False.elim)
    fun t ⟨hc', hy', _, hh, hf, _⟩ =>
      ⟨⟨mi, X, Xc, hc', ht.of_win hf hc.scrT.nowrap, hy',
        (hh _ (by decide)).trans hv, hv', hw, hw', hR⟩, (hh _ (by decide)).trans hn⟩

private theorem count_next_post (Sq : MontS) {p : (XPub × Nat) × Nat} {s : State}
    (h : CountPre Sq.bd p s) (h1 : 1 ≤ p.2) (h4 : p.2 ≤ 4) :
    WP isa (.block squaresNext) s fun t =>
      CountPre Sq.bd (p.1, p.2 - 1) t ∧ t.zf = some (decide (p.2 - 1 = 0)) := by
  obtain ⟨mi, X, Xc, hc, _⟩ := h.1
  refine WP.mono (squaresNext_ok hc h.2 h1 h4) fun t ⟨hm, hz, hk⟩ => ?_
  exact ⟨⟨count_window h.1 hm hk, by rw [hm, word_writeW_self]⟩, hz⟩

private theorem squares_ct (Sq : MontS) :
    RelCT isa (Two (WindowPre Sq.bd)) (squares Sq.mm) (Two (WindowPre Sq.bd)) := by
  have pin : ∀ p s, WindowPre Sq.bd p s → s.gpr .rdi = off p.1.B p.1.o := by
    intro p s ⟨_, _, _, hc, _⟩
    exact hc.good.rdi
  have sq : RelCT isa (Two (CountPre Sq.bd)) Sq.mm (Two (CountPre Sq.bd)) :=
    two_post (two_map (fun p : (XPub × Nat) × Nat => p.1.1.ws)
      (fun _ _ ⟨⟨mi, _, _, hc, _⟩, _⟩ => ⟨mi, hc.good, Nat.le_refl _⟩) Sq.ct)
      (fun _ _ h => square_count_post Sq h)
  unfold squares
  refine RelCT.seq (two_piece (Ψ := fun p s => CountPre Sq.bd (p, 4) s)
    [.rdi] (fun p s t hs ht r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact (pin p s hs).trans (pin p t ht).symm) (by taint_decide) ?_) ?_
  · intro p s h
    have h0 := h
    obtain ⟨mi, X, Xc, hc, _⟩ := h
    refine WP.mono (squaresInit_ok hc) fun t ⟨hm, hk⟩ => ?_
    exact ⟨count_window h0 hm hk, by rw [hm, word_writeW_self]⟩
  · have loop := two_loop (body := .seq Sq.mm (.block squaresNext)) (cond := .ne) (Φ := fun (p : XPub × Nat) j s => CountPre Sq.bd (p, 4 - j) s)
      (Ψ := WindowPre Sq.bd) (fun _ => 4) ?_ ?_
    exact loop.mono (by
      rintro s t ⟨p, hs, ht⟩
      exact ⟨p, ⟨by decide, hs⟩, ⟨by decide, ht⟩⟩) (fun _ _ h => h)
    · refine RelCT.seq (two_post (Ψ := fun (p : (XPub × Nat) × Nat) s =>
        p.2 < 4 ∧ CountPre Sq.bd (p.1, 4 - p.2) s)
        (two_map (fun p : (XPub × Nat) × Nat => (p.1, 4 - p.2))
        (fun _ _ h => h.2) (sq.mono (fun _ _ h => h) (fun _ _ _ => True.intro))) ?_) ?_
      · intro p s ⟨hj, h⟩
        exact WP.mono (square_count_post Sq h) fun t ht => ⟨hj, ht⟩
      · exact two_taint [.rdi] (fun p s t hs ht r hr => by
          obtain rfl := List.mem_singleton.mp hr
          exact (pin p.1 s hs.2.1).trans (pin p.1 t ht.2.1).symm) (by taint_decide)
    · intro p j s hj h
      refine WP.seq (WP.mono (square_count_post Sq h) fun t ht => ?_)
      refine WP.mono (count_next_post Sq ht (by omega) (by omega)) fun u ⟨hu, hz⟩ => ?_
      refine ⟨?_, ?_, fun _ => hu.1⟩
      · by_cases hn : j + 1 < 4
        · have hn' : 4 - j - 1 ≠ 0 := by omega
          simp [eval, hz, hn, hn']
        · have hn' : 4 - j - 1 = 0 := by omega
          simp [eval, hz, hn, hn']
      · intro hj'
        simpa only [Nat.sub_sub, Nat.add_comm j 1] using hu

theorem window_ct (M : Mont) (Sq : MontS) :
    RelCT isa (Two (WindowPre Sq.bd)) (seqs (window Sq.mm M.mm)) (fun _ _ => True) := by
  unfold window seqs
  refine RelCT.seq (squares_ct Sq) ?_
  refine RelCT.seq (two_piece (Ψ := fun p s => SelectPre (p.1, p.2 / 16 % 16) s ∧
      ∃ minv X Xc, CExpCtx s (off p.1.B p.1.o) p.1.wx minv X Xc ∧
        CTab s.mem (off p.1.B p.1.o) p.1.wx X False 0)
    [.rdi] (pins_rdi (fun p : XPub × Nat => off p.1.B p.1.o)
      (fun _ _ ⟨_, _, _, hc, _⟩ => hc.good.rdi)) (by taint_decide) ?_) ?_
  · intro p s h
    rcases h with ⟨minv, X, Xc, hc, ht, hy, hv, hv', hrest⟩
    refine WP.and (mid_post ⟨minv, X, Xc, hc, ht, hy, hv, hv', hrest⟩) (WP.mono (winMid_ok hc hv (by omega)) fun t ⟨hm, hk⟩ => ?_)
    have hf : Frm (off p.1.B p.1.o) (crtWinRanges p.1.wx) s.mem t.mem := by
      rw [hm]
      exact (Frm.of_outside (writeW_outside _ _ _ (d := 8 * Crt.sV) (by decide)) (by simp [crtWinRanges])).trans
        (Frm.of_outside (writeW_outside _ _ _ (d := 8 * Crt.sNib) (by decide)) (by simp [crtWinRanges]))
    exact ⟨minv, X, Xc, hc.of_win hf hk.2.2 (hk.gpr (by decide)), ht.of_win hf hc.scrT.nowrap⟩
  · refine RelCT.seq (two_post (Ψ := fun p s => s.gpr .rdi = off p.1.B p.1.o)
      (two_map (fun p : XPub × Nat => (p.1, p.2 / 16 % 16)) (fun _ _ h => h.1) (applyWindow_ct M)) ?_) ?_
    · intro p s ⟨⟨minv, X, Xc, hc, hw, hw', hv, ht, hn⟩, minv', X', Xc', hc2, htab⟩
      have heq : X' = X := hc2.n.symm.trans hc.n
      unfold applyWindow
      refine WP.seq (WP.mono (test_ok hc hv hn) fun t ⟨hm, hz, hk⟩ => ?_)
      have hc' := hc.of_win (hm ▸ Frm.refl _ _ _) hk.2.2 (hk.gpr (by decide))
      by_cases he : p.2 / 16 % 16 = 0
      · exact WP.ite true (by simp [eval, hz, he]) (fun _ => WP.block_nil hc'.good.rdi) (by simp)
      · refine WP.ite false (by simp [eval, hz, he]) (by simp) (fun _ => ?_)
        refine WP.seq (WP.mono (select_ok hc' hw hw' hv (hm ▸ ht) (hm ▸ hn)) fun u hu => ?_)
        exact WP.mono (M.mm_ok (o := aY) (a := aY) (b := Crt.aT) hu.1.good (Nat.le_refl _) hw (by omega)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hu.1.inv
          (by rw [hu.1.n, hu.2.1, hm, ← heq]; exact htab.lt _ hv)) (fun _ h => h.1.rdi)
    · exact rdi_ct (fun p : XPub × Nat => off p.1.B p.1.o) (fun _ _ h => h) (by taint_decide)

end VG.Proof.Dsa.X86_64.PublicPower
