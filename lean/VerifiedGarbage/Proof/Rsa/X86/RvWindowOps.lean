module

public import VerifiedGarbage.Proof.Rsa.X86.RvOps
public import VerifiedGarbage.Proof.Rsa.X86.RvSlots
public import VerifiedGarbage.Proof.Mont.X86.WindowWords

/-! # The window operations on the recovery workspace

The exponent's words shifted up by four bits, its top four bits into a
header word, and whether they name a table entry.
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys

abbrev liveExp : List Nat := [mY, mG, mR2, mBase, aO, aNg, aZ, aOne, aN]
abbrev slotsExp : List Nat := [sInv, sCnt, sTc, sCand]

section
variable {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
  {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat}

theorem KS.shiftUp_W {j : Nat} (h : KS g s0 A live AW liveW V ls s)
    (hj : j ∈ liveW) (hl : ∀ i ∈ live, i / 2 ≠ j) :
    WP isa (.block (VG.Impl.Mont.X86.Dynamic.shiftUp g.W (arr g.W j))) s fun t =>
      KS g s0 A live (upd AW j (AW j * 16 % 2 ^ (32 * g.W))) (j :: liveW) V ls t ∧
      Keeps opRegs s t := by
  have hjN := h.liveW_lt j hj
  have fit := h.wsW.arr_fit hjN
  simp only [S] at fit
  refine WP.mono (VG.Proof.Mont.X86.Dynamic.shiftUp_ok h.wsW.workspace g.W (arr g.W j) (by omega))
    fun t ⟨frame, value, rest⟩ => ?_
  have k : Keep g.B g.W [j] [] s.mem t.mem :=
    Keep.of_arr (d := 0) (by simpa using frame) (by unfold S; omega) (by simp)
  refine ⟨h.write_W k hjN (by simp) (rest.mono (by decide)) ?_ hl (by simp), rest.mono (by decide)⟩
  change val32 t.mem g.B (arr g.W j) g.W = _
  rw [value]
  change num s.mem g.B g.W j * 16 % _ = _
  rw [h.arrsW j hj]

theorem KS.windowTop_ok (h : KS g s0 A live AW liveW V ls s) (hj : wRc ∈ liveW) :
    WP isa (.block (windowTop g.n)) s fun t =>
      KS g s0 A live AW liveW (upd V sWin (AW wRc * 16 / 2 ^ (32 * g.W))) (sWin :: ls) t ∧
      Keeps opRegs s t := by
  have hjN := h.liveW_lt wRc hj
  have fit := h.wsW.arr_fit hjN
  simp only [S] at fit
  have pos : 0 < g.W := by simp only [Geo.W, wide]; omega
  unfold windowTop
  refine wp_movS (readSrc_sc h.ws.workspace (d := arr g.W wRc + 4 * (g.W - 1)) (by omega))
    fun u U _ => ?_
  have hu := h.of_rest U.keeps (by decide) U.mem
  refine wp_shr (by decide) fun v D _ => ?_
  have hv := hu.of_rest D.keeps (by decide) D.mem
  refine WP.mono (hv.storeSlot (d := sWin) (by decide) .eax) fun t ⟨ht, _, kt⟩ => ?_
  refine ⟨?_, ((U.keeps.mono (by decide) : Keeps opRegs s u).trans
    (D.keeps.mono (by decide))).trans (kt.mono (by decide))⟩
  have value : (v.gpr .eax).toNat = AW wRc * 16 / 2 ^ (32 * g.W) := by
    rw [D.gpr, U.gpr, VG.Proof.Mont.X86.Dynamic.shr28_toNat, ← h.arrsW wRc hj]
    obtain ⟨k, hk⟩ : ∃ k, g.W = k + 1 := ⟨g.W - 1, by omega⟩
    change w32 s.mem g.B (arr g.W wRc + 4 * (g.W - 1)) / 2 ^ 28 =
      val32 s.mem g.B (arr g.W wRc) g.W * 16 / 2 ^ (32 * g.W)
    rw [hk, VG.Proof.Mont.X86.Dynamic.val32_top_bits, Nat.add_sub_cancel]
  rw [value] at ht
  exact ht

theorem window_is_small : ∀ a < 16, ∀ j < 16,
    (((BitVec.ofNat 32 a ^^^ BitVec.ofNat 32 j) - 1) >>> 31).toNat = if a = j then 1 else 0 := by
  decide

theorem KS.windowIs_ok {j : Nat} (h : KS g s0 A live AW liveW V ls s) (hw : sWin ∈ ls)
    (small : V sWin < 16) (hj : j < 16) :
    WP isa (.block (windowIs j)) s fun t =>
      KS g s0 A live AW liveW (upd V sEq (if V sWin = j then 1 else 0)) (sEq :: ls) t ∧
      Keeps opRegs s t := by
  unfold windowIs
  refine wp_movS (h.readSlot hw) fun u U _ => ?_
  have hu := h.of_rest U.keeps (by decide) U.mem
  refine wp_logicS (.inr rfl) rfl fun v X => ?_
  have hv := hu.of_rest X.keeps (by decide) X.mem
  refine wp_subS rfl fun w D _ => ?_
  have hw' := hv.of_rest D.keeps (by decide) D.mem
  refine wp_shr (by decide) fun x R _ => ?_
  have hx := hw'.of_rest R.keeps (by decide) R.mem
  refine WP.mono (hx.storeSlot (d := sEq) (by decide) .eax) fun t ⟨ht, _, kt⟩ => ?_
  refine ⟨?_, ((((U.keeps.mono (by decide) : Keeps opRegs s u).trans (X.keeps.mono (by decide))).trans
    (D.keeps.mono (by decide))).trans (R.keeps.mono (by decide))).trans (kt.mono (by decide))⟩
  have value : (x.gpr .eax).toNat = if V sWin = j then 1 else 0 := by
    rw [R.gpr, D.gpr, X.gpr, U.gpr]
    simp only [reduceCtorEq, ↓reduceIte]
    exact window_is_small _ small _ hj
  rw [value] at ht
  exact ht

end
end VG.Proof.Rsa.X86.Recover
