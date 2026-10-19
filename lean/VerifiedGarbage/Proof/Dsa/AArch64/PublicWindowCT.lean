module
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
public import VerifiedGarbage.Impl.Dsa.AArch64.PublicPower
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtExp

import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTExp
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTExp
import VerifiedGarbage.Proof.Dsa.AArch64.PublicWindow
meta import VerifiedGarbage.Proof.Dsa.AArch64.PublicWindow
import VerifiedGarbage.Proof.Dsa.AArch64.PublicSelect
meta import VerifiedGarbage.Proof.Dsa.AArch64.PublicSelect
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
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTGPow
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChk
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
import VerifiedGarbage.Proof.Dsa.AArch64.PublicExponent
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Poly1305.Limbs64
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
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTGPow
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtChk
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
meta import VerifiedGarbage.Proof.Dsa.AArch64.PublicExponent
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Poly1305.Limbs64

/-! # Public window addresses and branches depend only on the exponent -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64.PublicPower
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64.PublicPower

/-- The digit, unlike the table values, is shared by both executions. -/
def SelectPre (p : XPub × Nat) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (X Xc : Nat), CExpCtx s (off p.1.B p.1.o) p.1.wx minv X Xc ∧
    2 ≤ p.1.wx ∧ p.1.wx < 2 ^ 30 ∧ p.2 < 16 ∧
    word s.mem (off p.1.B p.1.o) (8 * Crt.sTab) = off (off p.1.B p.1.o) (slot p.1.wx 8) ∧
    word s.mem (off p.1.B p.1.o) (8 * Crt.sNib) = BitVec.ofNat 64 p.2

def SelectRegs (p : XPub × Nat) (s : State) : Prop :=
  s.gpr .x12 = BitVec.ofNat 64 p.1.wx ∧
  s.gpr .x16 = off (off p.1.B p.1.o) (slot p.1.wx (8 + p.2)) ∧
  s.gpr .x17 = off (off p.1.B p.1.o) (slot p.1.wx Crt.aT)

theorem select_ct : RelCT isa (Two SelectPre) select (fun _ _ => True) := by
  unfold select
  refine RelCT.seq (two_piece (Ψ := SelectRegs) [.x0]
    (pins_x0B (fun p : XPub × Nat => off p.1.B p.1.o) (fun _ _ ⟨_, _, _, hc, _⟩ => hc.good.x0))
    (by unfold selectHead; taint_decide) (fun p s ⟨_, _, _, hc, _, hw', hv, ht, hn⟩ =>
      WP.mono (selectHead_ok hc hw' hv ht hn) (fun _ h => ⟨h.1.1, h.1.2.1, h.1.2.2.1⟩))) ?_
  exact two_taint [.x12, .x16, .x17] (pins_of
    (fun p r => if r = .x12 then BitVec.ofNat 64 p.1.wx else
      if r = .x16 then off (off p.1.B p.1.o) (slot p.1.wx (8 + p.2)) else
        off (off p.1.B p.1.o) (slot p.1.wx Crt.aT)) (by
      intro p s h r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h.1
      · exact h.2.1
      · exact h.2.2)) (by taint_decide)

theorem applyWindow_ct (M : Mont) : RelCT isa (Two SelectPre) (applyWindow M.mm) (fun _ _ => True) := by
  unfold applyWindow
  refine RelCT.seq (two_piece (Ψ := fun p s => SelectPre p s ∧ s.gpr .x3 = BitVec.ofNat 64 p.2) [.x0]
    (pins_x0B (fun p : XPub × Nat => off p.1.B p.1.o) (fun _ _ ⟨_, _, _, hc, _⟩ => hc.good.x0))
    (by taint_decide) ?_) ?_
  · intro p s ⟨minv, X, Xc, hc, hw, hw', hv, ht, hn⟩
    refine WP.mono (test_ok hc hn) fun t ⟨⟨h3, hm⟩, hk⟩ => ?_
    exact ⟨⟨minv, X, Xc, hc.of_win (hm ▸ Frm.refl _ _ _) hk.wr (hk.gpr .x0 (by decide)),
      hw, hw', hv, hm ▸ ht, hm ▸ hn⟩, h3⟩
  refine two_ite (fun p s t hs ht => by
    rw [eval_zero_x3 hs.2 (by have := hs.1; obtain ⟨_, _, _, _, _, _, hv, _⟩ := this; omega),
      eval_zero_x3 ht.2 (by have := ht.1; obtain ⟨_, _, _, _, _, _, hv, _⟩ := this; omega)]) ?_ ?_
  · exact two_taint [] (by intro p s t hs ht r hr; cases hr) (by taint_decide)
  · refine (RelCT.seq (two_post (Ψ := fun p s => GoodW p.1.ws s)
      (two_map (fun p : XPub × Nat => p) (fun _ _ h => h.1.1) select_ct) ?_)
      (two_map (fun p : XPub × Nat => p.1.ws) (fun _ _ h => h)
        (M.ct (o := aY) (a := aY) (b := Crt.aT) (by unfold MmUse; decide))))
    intro p s ⟨⟨⟨minv, X, Xc, hc, hw, hw', hv, ht, hn⟩, _⟩, _⟩
    exact WP.mono (select_ok hc hw hw' hv ht hn) (fun _ h => ⟨minv, h.1.good, Nat.le_refl _⟩)

/-- A window's input pins the shifted public exponent byte. -/
def WindowPre (p : XPub × Nat) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (X Xc : Nat), CExpCtx s (off p.1.B p.1.o) p.1.wx minv X Xc ∧
    CTab s.mem (off p.1.B p.1.o) p.1.wx X False 0 ∧
    wv s.mem (off p.1.B p.1.o) (slot p.1.wx aY) p.1.wx < X ∧
    word s.mem (off p.1.B p.1.o) (8 * Crt.sV) = BitVec.ofNat 64 p.2 ∧
    p.2 < 2 ^ 56 ∧ 2 ≤ p.1.wx ∧ p.1.wx < 2 ^ 30 ∧ Nat.Coprime (2 ^ (64 * p.1.wx)) X

theorem square_post (M : Mont) {p : XPub × Nat} {s : State} (h : WindowPre p s) :
    WP isa (M.mm aY aY aY) s (WindowPre p) := by
  obtain ⟨minv, X, Xc, hc, ht, hy, hv, hv', hw, hw', hR⟩ := h
  exact WP.mono (crtSq_ok M (Q := False) (x := 0) (E := 0) hc hw hw' hR hy False.elim)
    fun t ⟨hc', hy', _, hh, hf, _⟩ => ⟨minv, X, Xc, hc', ht.of_win hf hc.scrT.nowrap, hy',
      (hh _ (by decide)).trans hv, hv', hw, hw', hR⟩

/-- After the window's digit: the selection's hypotheses, and the table. -/
def MidPost (p : XPub × Nat) (s : State) : Prop :=
  SelectPre (p.1, p.2 / 16 % 16) s ∧
    ∃ minv X Xc, CExpCtx s (off p.1.B p.1.o) p.1.wx minv X Xc ∧ CTab s.mem (off p.1.B p.1.o) p.1.wx X False 0

theorem mid_post {p : XPub × Nat} {s : State} (h : WindowPre p s) : WP isa (.block winMid) s (MidPost p) := by
  obtain ⟨minv, X, Xc, hc, ht, _, hv, hv', hw, hw', _⟩ := h
  refine WP.mono (winMid_ok hc hv (by omega)) fun t ⟨hm, hk⟩ => ?_
  have hf : Frm (off p.1.B p.1.o) (crtWinRanges p.1.wx) s.mem t.mem := by
    rw [hm]
    exact (Frm.of_outside (writeW_outside _ _ _ (d := 8 * Crt.sV) (by decide)) (by simp [crtWinRanges])).trans
      (Frm.of_outside (writeW_outside _ _ _ (d := 8 * Crt.sNib) (by decide)) (by simp [crtWinRanges]))
  have hc' := hc.of_win hf hk.wr (hk.gpr .x0 (by decide))
  have ht' := ht.of_win hf hc.scrT.nowrap
  exact ⟨⟨minv, X, Xc, hc', hw, hw', Nat.mod_lt _ (by decide), ht'.tab, by rw [hm, word_writeW_self]⟩,
    minv, X, Xc, hc', ht'⟩

theorem window_ct (M : Mont) : RelCT isa (Two WindowPre) (seqs (window M.mm)) (fun _ _ => True) := by
  have sq : RelCT isa (Two WindowPre) (M.mm aY aY aY) (Two WindowPre) :=
    two_post (two_map (fun p : XPub × Nat => p.1.ws)
      (fun _ _ ⟨minv, _, _, hc, _⟩ => ⟨minv, hc.good, Nat.le_refl _⟩)
      (M.ct (by unfold MmUse; decide))) (fun _ _ h => square_post M h)
  rw [window_eq]
  simp only [seqs]
  refine RelCT.seq sq (RelCT.seq sq (RelCT.seq sq (RelCT.seq sq ?_)))
  refine RelCT.seq (two_piece (Ψ := MidPost) [.x0] (pins_x0B (fun p : XPub × Nat => off p.1.B p.1.o)
      (fun _ _ ⟨_, _, _, hc, _⟩ => hc.good.x0)) (by unfold winMid; taint_decide) fun _ _ h => mid_post h) ?_
  refine RelCT.seq (two_post (Ψ := fun p s => s.gpr .x0 = off p.1.B p.1.o)
    (two_map (fun p : XPub × Nat => (p.1, p.2 / 16 % 16)) (fun _ _ h => h.1) (applyWindow_ct M)) ?_) ?_
  · intro p s ⟨⟨minv, X, Xc, hc, hw, hw', hv, ht, hn⟩, minv', X', Xc', hc2, htab⟩
    have heq : X' = X := hc2.n.symm.trans hc.n
    unfold applyWindow
    refine WP.seq (WP.mono (test_ok hc hn) fun t ⟨⟨h3, hm⟩, hk⟩ => ?_)
    have hc' := hc.of_win (hm ▸ Frm.refl _ _ _) hk.wr (hk.gpr .x0 (by decide))
    have hz := eval_zero_x3 h3 (show p.2 / 16 % 16 < 2 ^ 64 by omega)
    by_cases he : p.2 / 16 % 16 = 0
    · exact WP.ite true (by rw [hz]; simp [he]) (fun _ => WP.block_nil hc'.good.x0) (by simp)
    · refine WP.ite false (by rw [hz]; simp [he]) (by simp) (fun _ => ?_)
      refine WP.seq (WP.mono (select_ok hc' hw hw' hv (hm ▸ ht) (hm ▸ hn)) fun u hu => ?_)
      exact WP.mono (M.mm_ok (o := aY) (a := aY) (b := Crt.aT) hu.1.good (Nat.le_refl _) hw (by omega)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hu.1.inv
        (by rw [hu.1.n, hu.2.1, hm, ← heq]; exact htab.lt _ hv)) (fun _ h => h.1.x0)
  · exact x0_ct (fun p : XPub × Nat => off p.1.B p.1.o) (fun _ _ h => h) (by taint_decide)

end VG.Proof.Dsa.AArch64.PublicPower
