module

meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
public import VerifiedGarbage.Proof.Dsa.X86_64.ReadyCallCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReadyCallCT
import VerifiedGarbage.Proof.Dsa.X86_64.PublicPower
meta import VerifiedGarbage.Impl.Dsa.X86_64.PublicPower
meta import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Dsa.X86_64.SetupCT
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Dsa.X86_64.Prepare
import VerifiedGarbage.Proof.Dsa.X86_64.Load
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Dsa.X86_64.SetupCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Dsa.X86_64.Prepare
meta import VerifiedGarbage.Proof.Dsa.X86_64.Load
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Dsa.X86_64.PowerCT
public import VerifiedGarbage.Impl.Dsa.X86_64.PublicPower
import VerifiedGarbage.Proof.Dsa.X86_64.EncodePower
meta import VerifiedGarbage.Proof.Dsa.X86_64.PowerCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.PublicPower
meta import VerifiedGarbage.Proof.Dsa.X86_64.EncodePower
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Bignum.Math

/-! ### `Dsa.X86_64.PublicCallCT`, which only this module used -/

section

/-! ### `Dsa.X86_64.PublicPowerCT`, which only this module used -/

section

/-! ### `Dsa.X86_64.PublicExponentCT`, which only this module used -/

section

/-! ### `Dsa.X86_64.PublicWindowCT`, which only this module used -/

section

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

theorem mid_post {bd : Nat → Nat → Nat} {p : XPub × Nat} {s : State} (h : WindowPre bd p s) :
    WP isa (.block [.mov .rdx (.mem (hdr Crt.sV)), .mov .rax (.reg .rdx), .alu .add .rax (.reg .rax),
      .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
      .store (hdr Crt.sV) .rax, .shift .shr .rdx 4, .alu .and .rdx (.imm 15),
      .store (hdr Crt.sNib) .rdx]) s (SelectPre (p.1, p.2 / 16 % 16)) := by
  obtain ⟨minv, X, Xc, hc, ht, _, hv, hv', hw, hw', _⟩ := h
  refine WP.mono (winMid_ok hc hv (by omega_using [hv'])) fun t ⟨hm, hk⟩ => ?_
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
      refine WP.mono (count_next_post Sq ht (by omega) (by omega_using [])) fun u ⟨hu, hz⟩ => ?_
      refine ⟨?_, ?_, fun _ => hu.1⟩
      · by_cases hn : j + 1 < 4
        · have hn' : 4 - j - 1 ≠ 0 := by omega_using [hn]
          simp [eval, hz, hn, hn']
        · have hn' : 4 - j - 1 = 0 := by omega_using [hn]
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
    refine WP.and (mid_post ⟨minv, X, Xc, hc, ht, hy, hv, hv', hrest⟩) (WP.mono (winMid_ok hc hv (by omega_using [hv'])) fun t ⟨hm, hk⟩ => ?_)
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
        exact WP.mono (M.mm_ok (o := aY) (a := aY) (b := Crt.aT) hu.1.good (Nat.le_refl _) hw (by omega_using [hw'])
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hu.1.inv
          (by rw [hu.1.n, hu.2.1, hm, ← heq]; exact htab.lt _ hv)) (fun _ h => h.1.rdi)
    · exact rdi_ct (fun p : XPub × Nat => off p.1.B p.1.o) (fun _ _ h => h) (by taint_decide)

end VG.Proof.Dsa.X86_64.PublicPower

end

end

/-! # Public exponentiation leaks only its public exponent and layout -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.PublicPower
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64.PublicPower

/-- Fixed public byte through its two windows. -/
def WinI (bd : Nat → Nat → Nat) (p : XPub × Nat) (j : Nat) (s : State) : Prop :=
  ∃ (t₀ : State) (minv : BitVec 64) (X Xc E : Nat),
    CWinInv t₀ (off p.1.B p.1.o) p.1.wx minv X Xc (bd X (2 ^ (64 * p.1.wx))) False 0 E p.2 j s ∧
    2 ≤ p.1.wx ∧ p.1.wx < 2 ^ 30 ∧ Nat.Coprime (2 ^ (64 * p.1.wx)) X ∧ Xc < X ∧ p.2 < 256

theorem wins_ct (M : Mont) (Sq : MontS) :
    RelCT isa (Two fun p s => 0 < 2 ∧ WinI Sq.bd p 0 s) (.loop (seqs (window Sq.mm M.mm)) .ne)
      (Two fun p s => WinI Sq.bd p 2 s) := by
  apply two_loop (Φ := WinI Sq.bd) (fun _ => 2)
  · apply two_map (fun q : (XPub × Nat) × Nat => (q.1.1, q.1.2 * 16 ^ q.2)) ?_ (window_ct M Sq)
    intro q s ⟨hj, t₀, minv, X, Xc, E, hI, hw, hw', hR, _, hv⟩
    have hp : 16 ^ q.2 ≤ 16 := by rcases (show q.2 = 0 ∨ q.2 = 1 by omega_using [hj]) with h | h <;> rw [h] <;> decide
    exact ⟨minv, X, Xc, hI.ctx, hI.tab, hI.ylt, hI.v,
      by have := Nat.mul_le_mul_left q.1.2 hp; omega, hw, hw', hR⟩
  · intro p j s hj ⟨t₀, minv, X, Xc, E, hI, hw, hw', hR, hXN, hv⟩
    exact WP.mono (crtWinStep_ok M Sq hw hw' hR hv hj hI) fun _ ⟨hz, hI'⟩ =>
      ⟨eval_ne_count hj hz, fun _ => ⟨t₀, minv, X, Xc, E, hI', hw, hw', hR, hXN, hv⟩,
        fun h => h ▸ ⟨t₀, minv, X, Xc, E, hI', hw, hw', hR, hXN, hv⟩⟩

def CBytesInv (bd : Nat → Nat → Nat) (a : BPub × List Byte) (i : Nat) (s : State) : Prop :=
  ∃ (t₀ : State) (minv : BitVec 64) (X Xc : Nat),
    CByteInv t₀ (off a.1.x.B a.1.x.o) a.1.x.wx minv X Xc (bd X (2 ^ (64 * a.1.x.wx))) False 0 a.1.ptr a.2.length a.2 i s ∧ 2 ≤ a.1.x.wx ∧
    a.1.x.wx < 2 ^ 30 ∧ Nat.Coprime (2 ^ (64 * a.1.x.wx)) X ∧ Xc < X ∧
    a.2.length = a.1.len ∧ a.2.length < 2 ^ 31 ∧ Src t₀ a.1.x.B a.1.x.Z a.1.ptr a.2 ∧
    ∀ i < a.2.length, slot a.1.x.wx 8 + tabBytes a.1.x.wx ≤ ofs (off a.1.x.B a.1.x.o) (a.1.ptr + BitVec.ofNat 64 i)

/-- After the loads of the byte's address. -/
def CHeadMid (bd : Nat → Nat → Nat) (q : (BPub × List Byte) × Nat) (s : State) : Prop :=
  q.2 < q.1.1.len ∧ CBytesInv bd q.1 q.2 s ∧ s.gpr .rax = q.1.1.ptr ∧ s.gpr .rcx = BitVec.ofNat 64 q.2

theorem pins_cBytes {bd : Nat → Nat → Nat} :
    Pins (fun (q : (BPub × List Byte) × Nat) s => q.2 < q.1.1.len ∧ CBytesInv bd q.1 q.2 s) [.rdi] :=
  pins_rdi (fun q : (BPub × List Byte) × Nat => off q.1.1.x.B q.1.1.x.o) fun _ _ ⟨_, _, _, _, _, hI, _⟩ => hI.ctx.good.rdi

theorem pins_cHeadMid {bd : Nat → Nat → Nat} : Pins (CHeadMid bd) [.rdi, .rax, .rcx] := by
  rintro q s₁ s₂ ⟨-, ⟨_, _, _, _, i₁, _⟩, a₁, c₁⟩ ⟨-, ⟨_, _, _, _, i₂, _⟩, a₂, c₂⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [i₁.ctx.good.rdi, i₂.ctx.good.rdi]
  · rw [a₁, a₂]
  · rw [c₁, c₂]

/-- One byte of the exponent leaks the same in runs with the same workspace
and the same public exponent bytes, pointer and length. -/
theorem crtByte_ct (M : Mont) (Sq : MontS) : RelCT isa (Two fun (q : (BPub × List Byte) × Nat) s => q.2 < q.1.1.len ∧ CBytesInv Sq.bd q.1 q.2 s)
    (seqs [.block [.mov .rax (.mem (hdr Crt.sExp)), .mov .rcx (.mem (hdr Crt.sI)),
        .movzx8 .rax { base := .rax, index := some .rcx }, .store (hdr Crt.sV) .rax, .mov32 .rax (.imm 2),
        .store (hdr Crt.sBit) .rax],
      .loop (seqs (window Sq.mm M.mm)) .ne,
      .block [.mov .rax (.mem (hdr Crt.sI)), .alu .add .rax (.imm 1), .store (hdr Crt.sI) .rax,
        .alu .cmp .rax (.mem (hdr Crt.sExpLen))]]) fun _ _ => True := by
  simp only [seqs]
  rw [crtByteHead_eq]
  have w₁ : ∀ (q : (BPub × List Byte) × Nat) s, q.2 < q.1.1.len ∧ CBytesInv Sq.bd q.1 q.2 s →
      WP isa (.block [.mov .rax (.mem (hdr Crt.sExp)), .mov .rcx (.mem (hdr Crt.sI))]) s (CHeadMid Sq.bd q) := by
    rintro q s ⟨hi, t₀, minv, X, Xc, hI, hrest⟩
    exact WP.mono (crtByteHead1_ok hI) fun t ⟨h1, h2, h3⟩ => ⟨hi, ⟨t₀, minv, X, Xc, h3, hrest⟩, h1, h2⟩
  have w₂ : ∀ (q : (BPub × List Byte) × Nat) s, CHeadMid Sq.bd q s →
      WP isa (.block [.movzx8 .rax { base := .rax, index := some .rcx }, .store (hdr Crt.sV) .rax,
        .mov32 .rax (.imm 2), .store (hdr Crt.sBit) .rax]) s fun t => 0 < 2 ∧ WinI Sq.bd (q.1.1.x, (q.1.2[q.2]?.getD 0).toNat) 0 t := by
    rintro q s ⟨hi, ⟨t₀, minv, X, Xc, hI, hw, hw', hR, hXN, hL, -, he, hout⟩, hax, hcx⟩
    have hi' : q.2 < q.1.2.length := by omega_arith
    exact WP.mono (crtByteHead2_ok rfl hi' he.rd he.val hout hI hax hcx) fun t ⟨_, _, hB⟩ =>
      ⟨by decide, t, minv, X, Xc, _, by simpa only [List.getElem?_eq_getElem hi', Option.getD_some] using hB, hw, hw', hR, hXN, (q.1.2[q.2]?.getD 0).isLt⟩
  have h₃ : RelCT isa (Two fun (p : XPub × Nat) s => WinI Sq.bd p 2 s)
      (.block [.mov .rax (.mem (hdr Crt.sI)), .alu .add .rax (.imm 1), .store (hdr Crt.sI) .rax,
        .alu .cmp .rax (.mem (hdr Crt.sExpLen))]) fun _ _ => True :=
    rdi_ct (fun p : XPub × Nat => off p.1.B p.1.o) (fun _ _ ⟨_, _, _, _, _, hI, _⟩ => hI.ctx.good.rdi) (by taint_decide)
  exact RelCT.seq (RelCT.block_append (RelCT.seq (two_piece _ pins_cBytes (by taint_decide) w₁)
      (two_piece _ pins_cHeadMid (by taint_decide) w₂)))
    (RelCT.seq (two_map (fun q : (BPub × List Byte) × Nat => (q.1.1.x, (q.1.2[q.2]?.getD 0).toNat)) (fun _ _ h => h) (wins_ct M Sq)) h₃)

def EPre (sp sl : Nat) (p : BPub × List Byte) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (X x y : Nat),
    SubCtx s p.1.x.B p.1.x.Z p.1.x.o p.1.x.w p.1.x.wx minv ∧ 2 ≤ p.1.x.wx ∧ p.1.x.wx ≤ p.1.x.w ∧ p.1.x.w < 2 ^ 30 ∧
    wv s.mem (off p.1.x.B p.1.x.o) (slot p.1.x.wx Public.aN) p.1.x.wx = X ∧
    ((word s.mem (off p.1.x.B p.1.x.o) (slot p.1.x.wx Public.aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 ∧
    X % 2 = 1 ∧ wv s.mem (off p.1.x.B p.1.x.o) (slot p.1.x.wx Crt.aXc) p.1.x.wx < X ∧
    wv s.mem (off p.1.x.B p.1.x.o) (slot p.1.x.wx Crt.aXc) p.1.x.wx % X = x * 2 ^ (64 * p.1.x.wx) % X ∧
    wv s.mem (off p.1.x.B p.1.x.o) (slot p.1.x.wx Public.aY) p.1.x.wx < X ∧
    wv s.mem (off p.1.x.B p.1.x.o) (slot p.1.x.wx Public.aY) p.1.x.wx % X = y * 2 ^ (64 * p.1.x.wx) % X ∧
    sp < 32 ∧ sl < 32 ∧ word s.mem p.1.x.B (8 * sp) = p.1.ptr ∧
    word s.mem p.1.x.B (8 * sl) = BitVec.ofNat 64 p.2.length ∧ p.2.length = p.1.len ∧ 1 ≤ p.2.length ∧
    p.2.length ≤ 1024 ∧ Src s p.1.x.B p.1.x.Z p.1.ptr p.2


theorem EPre.secret {sp sl : Nat} {p : BPub × List Byte} {s : State} (h : EPre sp sl p s) :
    VG.Proof.Bignum.X86_64.EPre sp sl p.1 s := by
  obtain ⟨minv, X, x, y, hrest⟩ := h
  exact ⟨minv, X, x, y, p.2, hrest⟩

theorem crtExpLoop_ct (M : Mont) (Sq : MontS) {sp sl : Nat} {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi, .rax]) (.block [.mov .rdx (.mem (Crt.ws .rax sp)),
      .store (hdr Crt.sExp) .rdx, .mov .rdx (.mem (Crt.ws .rax sl)), .store (hdr Crt.sExpLen) .rdx,
      .mov32 .rdx (.imm 0), .store (hdr Crt.sI) .rdx]) hc).isSome = true) :
    RelCT isa (Two (EPre sp sl)) (VG.Impl.Dsa.X86_64.PublicPower.expLoop Sq.mm M.mm sp sl) (fun _ _ => True) := by
  unfold VG.Impl.Dsa.X86_64.PublicPower.expLoop
  refine RelCT.seq (two_post
    (Ψ := fun a s => 0 < a.1.len ∧ CBytesInv Sq.bd a 0 s) ?_ fun a s h => ?_) ?_
  · -- The start and the table.
    rw [← List.singleton_append]
    refine RelCT.seqs_append (by simp) (by simp [Crt.tabBuild, tabBuild_eq, tabPre]) (RelCT.seq (two_post (Ψ := fun a s => TPre 16 a.1.x s)
      ?_ fun _ _ h => by exact crtExpInit_tpre h.secret) (two_map (fun a : BPub × List Byte => a.1.x)
        (fun _ _ h => h) (tabBuild_ct M 16 (by decide) (by decide) (by taint_decide))))
    rw [crtExpInit_eq]
    exact RelCT.block_append (RelCT.seq (two_piece (Ψ := fun (a : BPub × List Byte) t => t.gpr .rdi = off a.1.x.B a.1.x.o ∧
        t.gpr .rax = a.1.x.B) [.rdi] ((pins_rdi (fun a : BPub × List Byte => off a.1.x.B a.1.x.o) (fun _ _ h => by
        obtain ⟨_, _, _, _, hc, _⟩ := h; exact hc.rdi))) (by taint_decide) fun _ _ h => crtLink_ok h.secret)
      (two_taint [.rdi, .rax] (pins_of (fun a r => if r = .rdi then off a.1.x.B a.1.x.o else a.1.x.B)
        fun a s h r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact h.1
          · exact h.2) hT))
  · obtain ⟨minv, X, x, y, hc, hw2, hwx, hw30, hn, hinv, hodd, hxl, -, hyl, -, hsp, hsl, hep, hel, hL, hL1, hL2,
      he⟩ := h
    have hPn := hc.scrT.nowrap
    have hBn := hc.scr.nowrap
    have hi := hc.hi
    have hlo := hc.lo
    have h256 : 256 ≤ slot a.1.x.wx 8 := by unfold slot hdrBytes; omega_arith
    have hout : ∀ i < a.2.length, slot a.1.x.wx 8 + tabBytes a.1.x.wx ≤ ofs (off a.1.x.B a.1.x.o) (a.1.ptr + BitVec.ofNat 64 i) :=
      fun i hi' => by
        have := he.out i hi'
        rcases ofs_rebase a.1.x.B (a.1.ptr + BitVec.ofNat 64 i) (o := a.1.x.o) (by omega_arith) with ⟨_, h2⟩ | ⟨h1, _⟩
        · omega_arith
        · omega_arith
    exact WP.mono (crtExpHead_ok M (Q := False) (x := 0) hc hw2 hwx hw30 hn hinv hodd hxl False.elim hyl False.elim
      hsp hsl hep hel he) fun t hI => ⟨by omega_arith, s, minv, X, _,
        CByteInv.mk hI.ctx hI.tab (Nat.lt_of_lt_of_le hI.ylt
          (Sq.le (by rw [← hn]; exact Nat.le_of_lt (wv_lt _ _ _ _)))) hI.y hI.idx hI.e hI.len hI.frm hI.keep,
        hw2, by omega_arith,
        VG.Proof.Bignum.coprime_pow2 hodd _, hxl, hL, by omega_arith, he, hout⟩
  unfold VG.Impl.Dsa.X86_64.PublicPower.byte
  refine (two_loop (Φ := CBytesInv Sq.bd) (Ψ := fun _ _ => True) (fun a => a.1.len) (crtByte_ct M Sq) ?_).mono
    (fun _ _ h => h) fun _ _ _ => trivial
  rintro a i s hi ⟨t₀, minv, X, Xc, hI, hw, hw', hR, hXN, hL, hL', he, hout⟩
  exact WP.mono (crtByte_ok M Sq hw hw' hR rfl hL' (by omega_arith) he.rd he.val hout hI)
    fun s' ⟨hz, hI'⟩ => ⟨eval_ne_count hi (by rw [hz, hL]), fun _ => ⟨t₀, minv, X, Xc, hI', hw, hw', hR, hXN, hL,
      hL', he, hout⟩, fun _ => trivial⟩


end VG.Proof.Dsa.X86_64.PublicPower

end

end

/-! # Timing of public exponentiation with secret bases -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.PublicPower
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64.PublicPower

def EncodedPre (p : PowerPublic × List Byte) (s : State) : Prop :=
  ∃ x : Nat, PowerInputs p.1 p.2 s ∧
    wv s.mem (off p.1.bytes.x.B p.1.bytes.x.o) (slot p.1.bytes.x.wx Crt.aXc) p.1.bytes.x.wx =
      x * 2 ^ (64 * p.1.bytes.x.wx) % p.1.modulus ∧
    wv s.mem (off p.1.bytes.x.B p.1.bytes.x.o) (slot p.1.bytes.x.wx aY) p.1.bytes.x.wx =
      2 ^ (64 * p.1.bytes.x.wx) % p.1.modulus

/-- Exponentiation and decoding together have a secret-independent trace. -/
theorem encodedPower_ct (M : Mont) (Sq : MontS) : RelCT isa (Two EncodedPre)
    (VG.Impl.Dsa.X86_64.PublicPower.encodedPower Sq.mm M.mm VG.Impl.Dsa.Layout.arg2 VG.Impl.Dsa.Layout.arg2Len)
    (fun _ _ => True) := by
  unfold VG.Impl.Dsa.X86_64.PublicPower.encodedPower
  refine RelCT.seq (two_post (Ψ := fun p s => GoodW p.1.bytes.x.ws s)
    (two_map (fun p : PowerPublic × List Byte => (p.1.bytes, p.2)) ?_ (crtExpLoop_ct M Sq (by taint_decide))) ?_)
    (two_map (fun p : PowerPublic × List Byte => p.1.bytes.x.ws) (fun _ _ h => h)
      (M.ct (by unfold MmUse; decide)))
  · intro p s ⟨x, ⟨hc, hm, _, hp, hl, hlen, h1, h2, hs⟩, hx, hy⟩
    refine ⟨p.1.minv, p.1.modulus, x, 1, hc, p.1.lower, p.1.fits, p.1.upper,
      hm.modulus, hm.inverse, p.1.odd, ?_, ?_, ?_, ?_, by decide, by decide,
      hp, hl, hlen, h1, h2, hs⟩
    · rw [hx]; exact Nat.mod_lt _ (by have := p.1.greater; omega_using [this])
    · rw [hx, Nat.mod_mod]
    · rw [hy]; exact Nat.mod_lt _ (by have := p.1.greater; omega_using [this])
    · rw [hy, Nat.mod_mod, Nat.one_mul]
  · intro p s ⟨x, ⟨hc, hm, _, hp, hl, _, h1, h2, hs⟩, hx, hy⟩
    refine WP.mono (expLoop_ok M Sq (x := x) hc p.1.lower p.1.fits p.1.upper hm.modulus hm.inverse p.1.odd
      (by rw [hx]; exact Nat.mod_lt _ (by have := p.1.greater; omega_using [this]))
      (by rw [hx, Nat.mod_mod])
      (by rw [hy]; exact Nat.mod_lt _ (by have := p.1.greater; omega_using [this]))
      (by rw [hy, Nat.mod_mod]) (by decide) (by decide) hp hl h1 h2 hs)
      fun t ⟨ht, _⟩ => ⟨p.1.minv, ht.good, Nat.le_refl _⟩

/-- Prepared ordinary bases for the complete encode/exponentiate/decode core. -/
def PowerCorePre (p : PowerPublic × List Byte) (s : State) : Prop :=
  PowerInputs p.1 p.2 s ∧
    wv s.mem (off p.1.bytes.x.B p.1.bytes.x.o) (slot p.1.bytes.x.wx aR2) p.1.bytes.x.wx =
      2 ^ (128 * p.1.bytes.x.wx) % p.1.modulus

/-- The whole power core is constant time for secret bases and fixed public exponents. -/
theorem powerCore_ct (M : Mont) (Sq : MontS) : RelCT isa (Two PowerCorePre)
    (VG.Impl.Dsa.X86_64.PublicPower.powerCore Sq.mm M.mm VG.Impl.Dsa.Layout.arg2 VG.Impl.Dsa.Layout.arg2Len)
    (fun _ _ => True) := by
  unfold VG.Impl.Dsa.X86_64.PublicPower.powerCore
  refine RelCT.seq (two_post (Ψ := EncodedPre)
    (two_map (fun p : PowerPublic × List Byte => p.1.product) ?_ (encodePower_ct M)) ?_)
    (encodedPower_ct M Sq)
  · intro p s ⟨⟨_, hm, hone, _⟩, hr2⟩
    refine ⟨hm, ?_⟩
    intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · dsimp only [PowerPublic.product]
      rw [hr2]; exact Nat.mod_lt _ (by have := p.1.greater; omega_using [this])
    · dsimp only [PowerPublic.product]
      rw [hone]; exact p.1.greater
  · intro p s ⟨⟨hc, hm, hone, hp, hl, hlen, h1, h2, hs⟩, hr2⟩
    rw [show 128 * p.1.bytes.x.wx = 64 * p.1.bytes.x.wx + 64 * p.1.bytes.x.wx by omega_using [], Nat.pow_add] at hr2
    refine WP.mono (encodePower_ok M hm (Nat.le_refl _) p.1.lower
      (by have := p.1.fits; have := p.1.upper; omega_arith) p.1.greater p.1.odd rfl hr2 hone)
      fun t ⟨hmt, hx, hy, htone, hf, hk⟩ => ?_
    have hct := arrays_context hc hf (by decide) hk
    have hfw := arrays_work hf (by decide)
    exact ⟨_, ⟨hct, hmt, htone, (work_parent hc hfw (by decide)).trans hp,
      (work_parent hc hfw (by decide)).trans hl, hlen, h1, h2, work_source hc hfw hk hs⟩, hx, hy⟩


end VG.Proof.Dsa.X86_64.PublicPower

end

end

/-! # Public exponent bytes across Montgomery setup and input loading -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.PublicPower
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Impl.Dsa.X86_64.PublicPower

def PowerCallBytes (p : PowerCallPublic × List Byte) (s : State) : Prop := ∃ bb : List Byte,
  word s.mem p.1.x.B (8 * arg) = p.1.base ∧ word s.mem p.1.x.B (8 * argLen) = BitVec.ofNat 64 bb.length ∧
  word s.mem p.1.x.B (8 * arg2) = p.1.bytes.ptr ∧ word s.mem p.1.x.B (8 * arg2Len) = BitVec.ofNat 64 p.2.length ∧
  bb.length = p.1.baseLen ∧ p.2.length = p.1.bytes.len ∧
  Src s p.1.x.B p.1.x.Z p.1.base bb ∧ Src s p.1.x.B p.1.x.Z p.1.bytes.ptr p.2

def PowerCallPre (p : PowerCallPublic × List Byte) (s : State) : Prop :=
  SubCtx s p.1.x.B p.1.x.Z p.1.x.o p.1.x.w p.1.x.wx p.1.minv ∧
  ModCtx s (off p.1.x.B p.1.x.o) (slot p.1.x.wx 8) p.1.x.wx p.1.minv p.1.modulus ∧ PowerCallBytes p s

def PowerCallPrepared (p : PowerCallPublic × List Byte) (s : State) : Prop := PowerCallPre p s ∧
  wv s.mem (off p.1.x.B p.1.x.o) (slot p.1.x.wx aOne) p.1.x.wx = 1 ∧
  wv s.mem (off p.1.x.B p.1.x.o) (slot p.1.x.wx aR2) p.1.x.wx = 2 ^ (128 * p.1.x.wx) % p.1.modulus

theorem PowerCallBytes.frame {p : PowerCallPublic × List Byte} {s t : State} (h : PowerCallBytes p s)
    (hc : SubCtx s p.1.x.B p.1.x.Z p.1.x.o p.1.x.w p.1.x.wx p.1.minv)
    (hf : Frm (off p.1.x.B p.1.x.o) (workRanges p.1.x.wx) s.mem t.mem) (hk : Keep mmRegs s t) :
    PowerCallBytes p t := by
  obtain ⟨bb, hp, hl, hep, hel, hbl, helen, hb, he⟩ := h
  exact ⟨bb, (work_parent hc hf (by decide)).trans hp, (work_parent hc hf (by decide)).trans hl,
    (work_parent hc hf (by decide)).trans hep, (work_parent hc hf (by decide)).trans hel,
    hbl, helen, work_source hc hf hk hb, work_source hc hf hk he⟩

theorem powerCall_prepare (M : Mont) {p : PowerCallPublic × List Byte} {s : State} (h : PowerCallPre p s) :
    WP isa (Arithmetic.constants M.mm) s (PowerCallPrepared p) := by
  refine WP.mono (prepare_ok M h.1 p.1.lower p.1.width48 p.1.greater p.1.odd h.2.1.modulus h.2.1.inverse)
    fun t ⟨hc, hm, hone, hr2, hf, hk⟩ => ?_
  exact ⟨⟨hc, hm, h.2.2.frame h.1 hf hk⟩, hone, hr2⟩

theorem powerCall_load {p : PowerCallPublic × List Byte} {s : State} (h : PowerCallPrepared p s) :
    WP isa (Arithmetic.load aX arg argLen) s (PowerCorePre (p.1.toPowerPublic, p.2)) := by
  obtain ⟨⟨hc, hm, bb, hp, hl, hep, hel, hbl, helen, hb, he⟩, hone, hr2⟩ := h
  have hb1 : 1 ≤ bb.length := hbl ▸ p.1.basePositive
  have hbw : (bb.length + 7) / 8 ≤ p.1.x.wx := hbl ▸ p.1.baseFits
  have hb31 : bb.length < 2 ^ 31 := by
    have hw48 : p.1.x.wx ≤ 48 := p.1.width48
    omega_using [hbw, hw48]
  refine WP.mono (load_ok hc p.1.lower p.1.fits p.1.upper (by decide) (by decide) (by decide) hp hl hb hb1 hb31 hbw)
    fun t ⟨hct, _, hf, hk⟩ => ?_
  have hfa : Arrays (off p.1.x.B p.1.x.o) p.1.x.wx [aX] s.mem t.mem :=
    Arrays.of_outside (List.mem_singleton_self aX) hf (Nat.le_refl _) (Nat.le_refl _)
  have hfw := arrays_work hfa (by decide)
  have hz := hc.good.scr.nowrap
  have hmt : ModCtx t (off p.1.x.B p.1.x.o) (slot p.1.x.wx 8) p.1.x.wx p.1.minv p.1.modulus := by
    refine ⟨hct.good, (hfa.wv_of_not_mem (by decide) (by decide) hz).trans hm.modulus, ?_⟩
    rw [hfa.word0_of_not_mem (by decide) (by decide) hz (by have := p.1.lower; omega_using [hb1, hbw])]
    exact hm.inverse
  refine ⟨⟨hct, hmt, (hfa.wv_of_not_mem (by decide) (by decide) hz).trans hone,
    (work_parent hc hfw (by decide)).trans hep, (work_parent hc hfw (by decide)).trans hel,
    helen, helen ▸ p.1.expPositive, helen ▸ p.1.expLimit, work_source hc hfw hk he⟩,
    (hfa.wv_of_not_mem (by decide) (by decide) hz).trans hr2⟩

theorem powerCall_ct (M : Mont) (Sq : MontS) : RelCT isa (Two PowerCallPre)
    (VG.Impl.Dsa.X86_64.PublicPower.power Sq.mm M.mm arg argLen arg2 arg2Len) (fun _ _ => True) := by
  unfold VG.Impl.Dsa.X86_64.PublicPower.power
  refine RelCT.seq (two_post (Ψ := PowerCallPrepared)
    (two_map (fun p : PowerCallPublic × List Byte => p.1.toPowerPublic.product) (fun p s h =>
      ⟨h.2.1, p.1.width48, p.1.greater, p.1.odd⟩) (constants_ct M)) (fun _ _ h => powerCall_prepare M h)) ?_
  refine RelCT.seq (two_post (Ψ := fun p s => PowerCorePre (p.1.toPowerPublic, p.2) s)
    (two_map (fun p : PowerCallPublic × List Byte => (⟨p.1.x, p.1.base, p.1.baseLen⟩ : BPub)) ?_
      (loadArr_ct (j := aX) (sp := arg) (sl := argLen) (by decide) (by taint_decide) (by taint_decide)))
    (fun _ _ h => powerCall_load h)) ?_
  · intro p s ⟨⟨hc, _, bb, hp, hl, _, _, hbl, _, hb, _⟩, _⟩
    refine ⟨p.1.minv, bb, hc, p.1.lower, p.1.fits, p.1.upper, by decide, by decide, by decide,
      hp, hl, hbl, hb, hbl ▸ p.1.basePositive, ?_, hbl ▸ p.1.baseFits⟩
    have hbw : (bb.length + 7) / 8 ≤ p.1.x.wx := hbl ▸ p.1.baseFits
    have hw48 : p.1.x.wx ≤ 48 := p.1.width48
    omega_using [hbw, hw48]
  · exact two_map (fun p : PowerCallPublic × List Byte => (p.1.toPowerPublic, p.2)) (fun _ _ h => h) (powerCore_ct M Sq)

end VG.Proof.Dsa.X86_64.PublicPower

end

end

/-! # Public exponent bytes across the DSA calling convention -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.PublicPower
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Impl.Dsa.X86_64.PublicPower

/-- Two readable byte strings at the same address and width agree. -/
theorem source_unique {s : State} {B p : Addr} {Z : Nat} {a b : List Byte}
    (ha : Src s B Z p a) (hb : Src s B Z p b) (hlen : a.length = b.length) : a = b := by
  apply List.ext_getElem hlen
  intro i hi hj
  exact (ha.val i hi).symm.trans (hb.val i hj)

def PowerFinishPre (p : PowerFinishPublic × List Byte) (s : State) : Prop :=
  PowerCallPre (p.1.toPowerCallPublic, p.2) s ∧ FinishPre p.1.result s

theorem powerFinish_ct (M : Mont) (Sq : MontS) : RelCT isa (Two PowerFinishPre)
    (.seq (VG.Impl.Dsa.X86_64.PublicPower.power Sq.mm M.mm arg argLen arg2 arg2Len) (seqs Core.finish)) (fun _ _ => True) := by
  refine RelCT.seq (two_post (Ψ := fun p s => FinishPre p.1.result s)
    (two_map (fun p : PowerFinishPublic × List Byte => (p.1.toPowerCallPublic, p.2)) (fun _ _ h => h.1) (powerCall_ct M Sq)) ?_)
    (two_map (fun p : PowerFinishPublic × List Byte => p.1.result) (fun _ _ h => h) finish_ct)
  intro p s ⟨⟨hc, hm, bb, hp, hl, hep, hel, hbl, helen, hb, he⟩, hf⟩
  exact WP.mono (power_ok M Sq hc p.1.lower p.1.width48 p.1.fits p.1.upper p.1.greater p.1.odd
    hm.modulus hm.inverse (by decide) (by decide) (by decide) (by decide)
    hp hl hb (hbl ▸ p.1.basePositive) (hbl ▸ p.1.baseFits)
    hep hel he (helen ▸ p.1.expPositive) (helen ▸ p.1.expLimit))
    fun t ⟨hct, _, _, hft, hkt⟩ => hf.work hc hct hft hkt

def CallPre (a b output : Operand) (p : Call3Public × List Byte) (s : State) : Prop :=
  Call3Pre a b output p.1 s ∧ Src s p.1.x.B p.1.x.Z p.1.bytes.ptr p.2 ∧ p.2.length = p.1.bytes.len

theorem callHead_public {p : Call3Public × List Byte} {s : State} {a b output : Operand}
    (ha : pointerFits a.pointer) (hb : pointerFits b.pointer) (ho : pointerFits output.pointer)
    (h : CallPre a b output p s) :
    WP isa (.block (callHead a b output p.1.x.o)) s (PowerFinishPre (p.1.toPowerFinishPublic, p.2)) := by
  obtain ⟨h, he, hlen⟩ := h
  refine WP.mono (callHead_run ha hb ho h) fun t ⟨⟨⟨hc, hm, bb, eb, hp, hl, hep, hel, hbl, helen, hs, hes⟩, hf⟩, hfr, hk⟩ => ?_
  have het := arguments_source hfr hk (Nat.le_trans (by decide) p.1.extent) he
  have eqb := source_unique hes het (helen.trans hlen.symm)
  subst eb
  exact ⟨⟨hc, hm, bb, hp, hl, hep, hel, hbl, helen, hs, hes⟩, hf⟩

theorem corePublicPow_ct (M : Mont) (Sq : MontS) {a b output : Operand} {o : Nat}
    (ha : pointerFits a.pointer) (hb : pointerFits b.pointer) (ho : pointerFits output.pointer)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (callHead a b output o)) hc).isSome = true) :
    RelCT isa (Two fun p s => CallPre a b output p s ∧ p.1.x.o = o)
      (Core.publicPow Sq.mm M.mm o a b output) (fun _ _ => True) := by
  change RelCT isa _ (.seq (.block (callHead a b output o))
    (.seq (VG.Impl.Dsa.X86_64.PublicPower.power Sq.mm M.mm arg argLen arg2 arg2Len) (seqs Core.finish))) _
  refine RelCT.seq (two_post (Ψ := fun p s => PowerFinishPre (p.1.toPowerFinishPublic, p.2) s)
    (two_map (fun p : Call3Public × List Byte => p.1) (fun _ _ h => h.1.1) (callHead_ct hT)) ?_)
    (two_map (fun p : Call3Public × List Byte => (p.1.toPowerFinishPublic, p.2)) (fun _ _ h => h) (powerFinish_ct M Sq))
  intro p s ⟨h, heq⟩
  rw [← heq]
  exact callHead_public ha hb ho h

def ReadyPublicPre (side : ModulusSide) (d : Nat) (a b : Operand)
    (p : ReadyCallPublic side d × List Byte) (s : State) : Prop :=
  ReadyCallPre side d a b p.1 s ∧ OperandBytes s p.1.layout.base activeBytes b p.2 ∧ p.2.length = p.1.exponentLen

theorem readyPublicPow_ct (M : Mont) (Sq : MontS) (side : ModulusSide) (d : Nat) (a b : Operand)
    (ha : pointerFits a.pointer) (hb : pointerFits b.pointer)
    (hpa : stablePointer a.pointer) (hpb : stablePointer b.pointer)
    (hd : d < 2 ^ 31)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi])
      (.block (callHead a b ⟨.local d, side.lengthField⟩ side.offset)) hc).isSome = true) :
    RelCT isa (Two (ReadyPublicPre side d a b))
      (Core.publicPow Sq.mm M.mm side.offset a b ⟨.local d, side.lengthField⟩) (fun _ _ => True) := by
  apply two_map (fun p : ReadyCallPublic side d × List Byte => (p.1.call a b, p.2)) ?_
    (corePublicPow_ct M Sq (output := ⟨.local d, side.lengthField⟩) ha hb hd hT)
  intro p s ⟨h, he, hlen⟩
  refine ⟨⟨readyCall_pre hpa hpb h, ?_, hlen⟩, rfl⟩
  have hp := h.1.publicPointer b.pointer hpb
  simpa only [hp, ReadyCallPublic.call, PowerCallPublic.x] using he.source

end VG.Proof.Dsa.X86_64.PublicPower
