module

public import VerifiedGarbage.Proof.Rsa.X86.RvOps
public import VerifiedGarbage.Proof.Rsa.X86.RvSlots
public import VerifiedGarbage.Proof.Mont.X86.WindowShift
import VerifiedGarbage.Proof.Rsa.X86.RvWrite
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Shift
import VerifiedGarbage.Proof.Framework.Omega

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
open VG.Proof.Mont.X86.Rt (PtrAt readSrc_ptr)

abbrev liveExp : List Nat := [mY, mG, mR2, mBase, aO, aNg, aZ, aOne, aN]
abbrev slotsExp : List Nat := [sInv, sCnt, sTc, sCand]

section
variable {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
  {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat}

theorem KS.shiftUp_W (h : KS g s0 A live AW liveW V ls s)
    (hj : wRc ∈ liveW) (hl : ∀ i ∈ live, i / 2 ≠ wRc) :
    WP isa VG.Impl.Rsa.X86.RecoverRt.shiftUp s fun t =>
      KS g s0 A live (upd AW wRc (AW wRc * 16 % 2 ^ (32 * g.W))) (wRc :: liveW) V ls t ∧
      Keeps opRegs s t := by
  have hw := h.rtW
  have fit := hw.ws.arr_fit (by decide : wRc < 22)
  have nowrap := hw.ws.workspace.nowrap
  have kn := kw_wid g.n
  have pos : 0 < VG.Proof.Rsa.X86.KeyRt.kw (16 * g.n + 24) := by rw [kn]; simp only [wide, width]; omega
  simp only [S] at fit
  unfold VG.Impl.Rsa.X86.RecoverRt.shiftUp
  refine WP.seq (VG.Proof.Rsa.X86.KeyRt.arrPtr_ok (VG.Proof.Rsa.X86.KeyRt.lenSrc hw) hw.lenLe hw.edi
    (r := .ebp) (t := .edx) (j := wRc) (by decide) (by decide) (by omega) fun u K m p _ => ?_)
  refine VG.Proof.Rsa.X86.KeyRt.bytesB_ok ((VG.Proof.Rsa.X86.KeyRt.lenSrc hw).keep K (by decide) m) hw.lenLe
    fun v K₂ m₂ e₂ => wp_movS rfl fun w U _ => WP.block_nil ?_
  have Kw : Keeps [.ebp, .edx, .ecx] s w :=
    ((K.mono (by decide)).trans (K₂.mono (by decide))).trans (U.keeps.mono (by decide))
  have mw : w.mem = s.mem := by rw [U.mem, m₂, m]
  refine WP.mono (VG.Proof.Bignum.X86.CrtRt.shiftLoop_ok (hw.rt.of_keeps Kw)
    (x := arr (VG.Proof.Rsa.X86.KeyRt.kw (16 * g.n + 24)) wRc) pos (by omega)
    (by rw [PtrAt, U.other _ (by decide), K₂.1 _ (by decide)]; exact p)
    (by rw [U.other _ (by decide)]; exact e₂) (by rw [U.gpr])) fun t ⟨O, value, Kt⟩ => ?_
  rw [mw] at O value
  rw [kn] at O value
  have rest : Keeps opRegs s t := (Kw.mono (by decide)).trans (Kt.mono (by decide))
  have k : Keep g.B g.W [wRc] [] s.mem t.mem :=
    Keep.of_arr (d := 0) (by simpa using O) (by unfold S; simp only [Geo.W]; omega) (by simp)
  refine ⟨h.write_W k (by decide) (by simp) rest ?_ hl (by simp), rest⟩
  change val32 t.mem g.B (arr g.W wRc) g.W = _
  rw [value]
  change num s.mem g.B g.W wRc * 16 % _ = _
  rw [h.arrsW wRc hj]

theorem KS.windowTop_ok (h : KS g s0 A live AW liveW V ls s) (hj : wRc ∈ liveW) :
    WP isa (.block VG.Impl.Rsa.X86.RecoverRt.windowTop) s fun t =>
      KS g s0 A live AW liveW (upd V sWin (AW wRc * 16 / 2 ^ (32 * g.W))) (sWin :: ls) t ∧
      Keeps opRegs s t := by
  have hw := h.rtW
  have fit := hw.ws.arr_fit (by decide : wRc < 22)
  have nowrap := hw.ws.workspace.nowrap
  have kn := kw_wid g.n
  have pos : 0 < VG.Proof.Rsa.X86.KeyRt.kw (16 * g.n + 24) := by rw [kn]; simp only [wide, width]; omega
  simp only [S] at fit
  unfold VG.Impl.Rsa.X86.RecoverRt.windowTop
  refine VG.Proof.Rsa.X86.KeyRt.arrPtr_ok (VG.Proof.Rsa.X86.KeyRt.lenSrc hw) hw.lenLe hw.edi
    (r := .eax) (t := .edx) (j := wRc) (by decide) (by decide) (by omega) fun u K m p e => ?_
  refine wp_addS rfl fun u₁ U₁ _ => wp_subS rfl fun u₂ U₂ _ => ?_
  have K₂ : Keeps [.eax, .edx] s u₂ := (K.trans (U₁.keeps.mono (by decide))).trans (U₂.keeps.mono (by decide))
  have ptr : PtrAt u₂ g.B .eax
      (arr (VG.Proof.Rsa.X86.KeyRt.kw (16 * g.n + 24)) wRc + 4 * (VG.Proof.Rsa.X86.KeyRt.kw (16 * g.n + 24) - 1)) := by
    rw [PtrAt, U₂.gpr, U₁.gpr, BitVec.toNat_sub, BitVec.toNat_add, p, e,
      show (12 : BitVec 32).toNat = 12 from rfl]
    omega
  have m₂ : u₂.mem = s.mem := by rw [U₂.mem, U₁.mem, m]
  refine wp_movS (readSrc_ptr (hw.rt.of_keeps K₂) ptr (d := 0) (by omega)) fun v D _ => ?_
  have KD : Keeps [.eax, .edx] s v := K₂.trans (D.keeps.mono (by decide))
  have hu := h.of_rest KD (by decide) (by rw [D.mem, m₂])
  refine wp_shr (by decide) fun x R _ => ?_
  have hx := hu.of_rest R.keeps (by decide) R.mem
  refine WP.mono (hx.storeSlot (d := sWin) (by decide) .eax) fun t ⟨ht, _, kt⟩ => ?_
  refine ⟨?_, ((KD.mono (by decide) : Keeps opRegs s v).trans
    (R.keeps.mono (by decide))).trans (kt.mono (by decide))⟩
  have value : (x.gpr .eax).toNat = AW wRc * 16 / 2 ^ (32 * g.W) := by
    rw [R.gpr, D.gpr, VG.Proof.Mont.X86.Dynamic.shr28_toNat, ← h.arrsW wRc hj, m₂, kn, Nat.add_zero]
    obtain ⟨k, hk⟩ : ∃ k, g.W = k + 1 := ⟨g.W - 1, by simp only [Geo.W, wide, width]; omega⟩
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
