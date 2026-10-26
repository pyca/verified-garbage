module

import VerifiedGarbage.Proof.Dsa.X86_64.SetupChoice
public import VerifiedGarbage.Proof.Dsa.X86_64.Frame
public import VerifiedGarbage.Spec.Dsa
import VerifiedGarbage.Proof.Dsa.X86_64.Load
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs

/-! # Preparing DSA arithmetic in a linked child workspace -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

/-- The setup frame includes the ordinary constant one. -/
def constantRanges (w : Nat) := (slot w aOne, 8 * (w + 2)) :: r2Ranges w

theorem constantRanges_work (w : Nat) : ∀ r ∈ constantRanges w,
    136 ≤ r.1 ∧ r.1 + r.2 ≤ slot w 8 + tabBytes w := by
  have h1 := slot_le (w := w) (show aOne < 8 by decide)
  have h2 := slot_le (w := w) (show aAcc < 8 by decide)
  have h3 := slot_le (w := w) (show aTmp < 8 by decide)
  have h4 := slot_le (w := w) (show aR2 < 8 by decide)
  simp only [constantRanges, r2Ranges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl) <;>
    simp only [slot, hdrBytes, aOne, aAcc, aTmp, aR2, sCnt, sFn] at * <;> omega

theorem constantRanges_modulus (w : Nat) : ∀ r ∈ constantRanges w,
    slot w aN + 8 * (w + 2) ≤ r.1 ∨ r.1 + r.2 ≤ slot w aN := by
  intro r hr
  simp only [constantRanges, List.mem_cons] at hr
  rcases hr with rfl | hr
  · exact slot_sep (w := w) (show aN ≠ aOne by decide)
  · exact r2Ranges_arr w (by decide) (by decide) (by decide) r hr

/-- Constants setup preserves the linked parent, both input buffers and
all modulus facts, including moduli with zero high limbs. -/
theorem prepare_ok (M : Mont) {s : State} {B : Addr} {Z o w wx m : Nat} {minv : BitVec 64}
    (hc : SubCtx s B Z o w wx minv) (hw2 : 2 ≤ wx) (hw48 : wx ≤ 48)
    (hm : 1 < m) (hodd : m % 2 = 1)
    (hn : wv s.mem (off B o) (slot wx aN) wx = m)
    (hinv : ((word s.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0) :
    WP isa (Arithmetic.constants M.mm) s fun t =>
      SubCtx t B Z o w wx minv ∧ ModCtx t (off B o) (slot wx 8) wx minv m ∧
      wv t.mem (off B o) (slot wx aOne) wx = 1 ∧
      wv t.mem (off B o) (slot wx aR2) wx = 2 ^ (128 * wx) % m ∧
      Frm (off B o) (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  refine WP.mono (constants_ok M hc.good (Nat.le_refl _) hw2 hw48 hn hm hodd hinv)
    fun t ⟨ht, h1, h2, hf, hk⟩ => ?_
  have hct := hc.of_frmT hf (constantRanges_work wx) hk.2.2 (hk.gpr (by decide))
  have hsep := constantRanges_modulus wx
  have hz := hc.good.scr.nowrap
  have hslot := slot_le (w := wx) (show aN < 8 by decide)
  have hmctx : ModCtx t (off B o) (slot wx 8) wx minv m := ⟨ht,
    (hf.wv_eq (fun r hr => by have := hsep r hr; omega) (by omega)).trans hn,
    by rw [hf.word_eq (fun r hr => by have := hsep r hr; omega) (by omega)]; exact hinv⟩
  refine ⟨hct, hmctx, h1, h2, ?_, hk⟩
  intro x hx
  apply hf x
  intro r hr
  have hb := constantRanges_work wx r hr
  have h := hx (136, slot wx 8 + tabBytes wx - 136) (List.mem_singleton_self _)
  have : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega
  omega

/-- Load one operand while retaining the modulus context and all other arrays. -/
theorem load_mod_ok {s : State} {B : Addr} {Z o w wx m : Nat} {minv : BitVec 64}
    (hc : SubCtx s B Z o w wx minv) (hm : ModCtx s (off B o) (slot wx 8) wx minv m)
    (hw2 : 2 ≤ wx) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    {j : Nat} (hj : j < 8) (hjn : j ≠ aN)
    {sp sl : Nat} (hsp : sp < 32) (hsl : sl < 32) {p : Addr} {bytes : List Byte}
    (hp : word s.mem B (8 * sp) = p)
    (hl : word s.mem B (8 * sl) = BitVec.ofNat 64 bytes.length)
    (hsrc : Src s B Z p bytes) (hk1 : 1 ≤ bytes.length) (hk' : bytes.length < 2 ^ 31)
    (hkw : (bytes.length + 7) / 8 ≤ wx) :
    WP isa (Arithmetic.load j sp sl) s fun t =>
      SubCtx t B Z o w wx minv ∧ ModCtx t (off B o) (slot wx 8) wx minv m ∧
      wv t.mem (off B o) (slot wx j) wx = Spec.Dsa.decodeBE bytes ∧
      (∀ i < 8, i ≠ j → wv t.mem (off B o) (slot wx i) wx = wv s.mem (off B o) (slot wx i) wx) ∧
      Frm (off B o) (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  refine WP.mono (load_ok hc hw2 hwx hw30 hj hsp hsl hp hl hsrc hk1 hk' hkw)
    fun t ⟨ht, hv, hf, hk⟩ => ?_
  have ha : Arrays (off B o) wx [j] s.mem t.mem :=
    Arrays.of_outside (List.mem_singleton_self j) hf (Nat.le_refl _) (Nat.le_refl _)
  have hnZ := hc.good.scr.nowrap
  have hnot : aN ∉ [j] := by simpa using Ne.symm hjn
  have hn := (ha.wv_of_not_mem (show aN < 8 by decide) hnot hnZ).trans hm.modulus
  have hi : ((word t.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 := by
    rw [ha.word0_of_not_mem (by decide) hnot hnZ (by omega)]
    exact hm.inverse
  refine ⟨ht, ⟨ht.good, hn, hi⟩, hv, ?_, arrays_work ha (by simpa using hj), hk⟩
  intro i hi hij
  exact ha.wv_of_not_mem hi (by simpa using hij) hnZ

end VG.Proof.Dsa.X86_64
