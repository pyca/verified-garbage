module

import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
public import VerifiedGarbage.Impl.Dsa.X86_64.PublicPower
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
meta import VerifiedGarbage.Impl.Dsa.X86_64.PublicPower
import VerifiedGarbage.Proof.Dsa.X86_64.PublicWindow
meta import VerifiedGarbage.Proof.Dsa.X86_64.PublicWindow
import VerifiedGarbage.Proof.Dsa.X86_64.PublicSelect
meta import VerifiedGarbage.Proof.Dsa.X86_64.PublicSelect
import VerifiedGarbage.Proof.Bignum.CrtMath
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
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
import VerifiedGarbage.Proof.Bignum.X86_64.Double
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Setup
import VerifiedGarbage.Proof.Bignum.X86_64.Store
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Dsa.X86_64.PublicExponent
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
meta import VerifiedGarbage.Proof.Bignum.CrtMath
meta import VerifiedGarbage.Proof.Bignum.LazyMath
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
meta import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.Copy
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
meta import VerifiedGarbage.Proof.Bignum.X86_64.Double
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
meta import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
meta import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Bignum.X86_64.Setup
meta import VerifiedGarbage.Proof.Bignum.X86_64.Store
meta import VerifiedGarbage.Proof.Bignum.X86_64.Valid
meta import VerifiedGarbage.Proof.Dsa.X86_64.PublicExponent
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

theorem window_ct (M : Mont) (Sq : MontS) :
    RelCT isa (Two (WindowPre Sq.bd)) (seqs (window Sq.mm M.mm)) (fun _ _ => True) := by
  have sq : RelCT isa (Two (WindowPre Sq.bd)) Sq.mm (Two (WindowPre Sq.bd)) :=
    two_post (two_map (fun p : XPub × Nat => p.1.ws)
      (fun _ _ ⟨minv, _, _, hc, _⟩ => ⟨minv, hc.good, Nat.le_refl _⟩)
      Sq.ct) (fun _ _ h => square_post Sq h)
  unfold window seqs
  refine RelCT.seq sq (RelCT.seq sq (RelCT.seq sq (RelCT.seq sq ?_)))
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
