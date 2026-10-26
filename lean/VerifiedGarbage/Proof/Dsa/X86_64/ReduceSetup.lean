module
public import VerifiedGarbage.Proof.Dsa.X86_64.Frame

import VerifiedGarbage.Proof.Dsa.X86_64.Prepare
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.X86_64.R2
import VerifiedGarbage.Proof.Bignum.Math
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs

/-! # Preparing the ordinary accumulator for streaming byte reduction -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

/-- Clearing an operand preserves the linked workspace and modulus. -/
theorem clear_mod_ok {s : State} {B : Addr} {Z o w wx m : Nat} {minv : BitVec 64}
    (hc : SubCtx s B Z o w wx minv) (hm : ModCtx s (off B o) (slot wx 8) wx minv m)
    (hw : 2 ≤ wx) (hw' : wx < 2 ^ 31) {j : Nat} (hj : j < 8) (hjn : j ≠ aN) :
    WP isa (Arithmetic.zero j) s fun t =>
      SubCtx t B Z o w wx minv ∧ ModCtx t (off B o) (slot wx 8) wx minv m ∧
      wv t.mem (off B o) (slot wx j) wx = 0 ∧
      Arrays (off B o) wx [j] s.mem t.mem ∧ Keep mmRegs s t := by
  refine WP.mono (zeroArr_ok hc.good (Nat.le_refl _) (by omega) hw' hj)
    fun t ⟨hv, hf, hk⟩ => ?_
  have ha : Arrays (off B o) wx [j] s.mem t.mem :=
    Arrays.of_outside (List.mem_singleton_self j) hf (Nat.le_refl _) (Nat.le_refl _)
  have ht := arrays_context hc ha (by simpa using hj) hk
  have hnZ := hc.good.scr.nowrap
  have hnot : aN ∉ [j] := by simpa using Ne.symm hjn
  refine ⟨ht, ⟨ht.good, (ha.wv_of_not_mem (by decide) hnot hnZ).trans hm.modulus, ?_⟩, (wv_eq_zero_iff _ _ _ _).mpr (fun i hi =>
      (wv_eq_zero_iff _ _ _ _).mp hv i (by omega)), ha, hk⟩
  rw [ha.word0_of_not_mem (by decide) hnot hnZ (by omega)]
  exact hm.inverse

/-- A public number of doublings retains the modulus and workspace. -/
theorem double_mod_ok {s : State} {B : Addr} {Z o w wx m c : Nat} {minv : BitVec 64}
    (hc : SubCtx s B Z o w wx minv) (hm : ModCtx s (off B o) (slot wx 8) wx minv m)
    (hw : 2 ≤ wx) (hw' : wx < 2 ^ 31) (hc1 : 1 ≤ c) (hc' : c < 2 ^ 31)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 c)
    (hlt : wv s.mem (off B o) (slot wx aR2) wx < m) :
    WP isa (doubles aN aAcc aTmp aR2 sCnt) s fun t =>
      SubCtx t B Z o w wx minv ∧ ModCtx t (off B o) (slot wx 8) wx minv m ∧
      wv t.mem (off B o) (slot wx aR2) wx =
        2 ^ c * wv s.mem (off B o) (slot wx aR2) wx % m ∧
      Frm (off B o) (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  refine WP.mono (doubles_ok hc.good.scr hc.rdi hc.hdr (Nat.le_refl _) hw hw'
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    hc1 hc' hcx (by rw [hm.modulus]; exact hlt)) fun t ⟨hv, hf, hh, hk⟩ => ?_
  have hfc : Frm (off B o) (constantRanges wx) s.mem t.mem :=
    hf.mono (fun r hr => List.mem_cons_of_mem _ hr)
  have ht := hc.of_frmT hfc (constantRanges_work wx) hk.2.2 (hk.gpr (by decide))
  have hz := hc.good.scr.nowrap
  have hn := (hf.r2_wv hz (by decide) (by decide) (by decide) (by decide)).trans hm.modulus
  have hi : ((word t.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 := by
    rw [hf.r2_word hz (by decide) (by decide) (by decide) (by decide)]
    exact hm.inverse
  rw [hm.modulus] at hv
  refine ⟨ht, ⟨ht.good, hn, hi⟩, hv, ?_, hk⟩
  intro x hx
  apply hfc x
  intro r hr
  have hb := constantRanges_work wx r hr
  have h := hx (136, slot wx 8 + tabBytes wx - 136) (List.mem_singleton_self _)
  have : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega
  omega

/-- Reduction starts with ordinary zero and multiplier 256R, even for
composite moduli with zero high limbs. -/
theorem reduceSetup_ok (M : Mont) {s : State} {B : Addr} {Z o w wx m : Nat}
    {minv : BitVec 64} (hc : SubCtx s B Z o w wx minv)
    (hw : 2 ≤ wx) (hw48 : wx ≤ 48) (hm : 1 < m) (hodd : m % 2 = 1)
    (hn : wv s.mem (off B o) (slot wx aN) wx = m)
    (hinv : ((word s.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0) :
    WP isa (Arithmetic.reduceSetup M.mm) s fun t =>
      SubCtx t B Z o w wx minv ∧ ModCtx t (off B o) (slot wx 8) wx minv m ∧
      wv t.mem (off B o) (slot wx aR2) wx = 256 * 2 ^ (64 * wx) % m ∧
      wv t.mem (off B o) (slot wx aY) wx = 0 ∧
      wv t.mem (off B o) (slot wx aX) wx = 0 ∧
      Frm (off B o) (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  have hw' : wx < 2 ^ 31 := by omega
  have hz := hc.good.scr.nowrap
  unfold Arithmetic.reduceSetup seqs
  refine WP.seq (WP.mono (prepare_ok M hc hw hw48 hm hodd hn hinv)
    fun u ⟨hcu, hmu, huone, hur2, hfu, hku⟩ => ?_)
  refine WP.seq (WP.mono (mont_step M hmu (Nat.le_refl _) hw hw'
    (by unfold MmUse; decide) (by rw [huone]; exact hm))
    fun v ⟨hmv, hlt, hv, hfv, hkv⟩ => ?_)
  rw [huone, Nat.mul_one, hur2, show 128 * wx = 64 * wx + 64 * wx by omega, Nat.pow_add, Nat.mod_mod] at hv
  have hvR : wv v.mem (off B o) (slot wx aR2) wx = 2 ^ (64 * wx) % m := by
    have e := VG.Proof.Bignum.mont_cancel (coprime_pow2 hodd (64 * wx)) hv
    simpa only [Nat.mod_eq_of_lt hlt] using e
  have hcv := arrays_context hcu hfv (by decide) hkv
  have hfw := hfu.trans (arrays_work hfv (by decide))
  have hkw := (hku.trans hkv).mono (show ∀ r ∈ mmRegs ++ mmRegs, r ∈ mmRegs by decide)
  refine WP.seq (WP.mono (WP.keep [.rcx] (Q := fun z =>
    z.gpr .rcx = 8 ∧ z.mem = v.mem) (by xrun) rfl) fun z ⟨⟨hcx, hmem⟩, hkz⟩ => ?_)
  have hcz : SubCtx z B Z o w wx minv := ⟨hcv.scr.congr hkz.2.2,
    (hkz.gpr (by decide)).trans hcv.rdi, hmem ▸ hcv.hdr, hmem ▸ hcv.link,
    hmem ▸ hcv.nw, hmem ▸ hcv.narr, hcv.lo, hcv.hi⟩
  have hmz : ModCtx z (off B o) (slot wx 8) wx minv m :=
    ⟨hcz.good, hmem ▸ hmv.modulus, hmem ▸ hmv.inverse⟩
  refine WP.seq (WP.mono (double_mod_ok hcz hmz hw hw' (by decide) (by decide)
    (c := 8) hcx (hmem ▸ hlt)) fun a ⟨hca, hma, ha, hfa, hka⟩ => ?_)
  rw [hmem, hvR, Nat.mul_mod_mod] at ha
  change wv a.mem (off B o) (slot wx aR2) wx = 256 * 2 ^ (64 * wx) % m at ha
  rw [hmem] at hfa
  refine WP.seq (WP.mono (clear_mod_ok hca hma hw hw' (by decide) (by decide))
    fun b ⟨hcb, hmb, hb, hfb, hkb⟩ => ?_)
  have bR := (hfb.wv_of_not_mem (show aR2 < 8 by decide) (by decide) hz).trans ha
  refine WP.mono (clear_mod_ok hcb hmb hw hw' (by decide) (by decide))
    fun t ⟨hct, hmt, ht, hft, hkt⟩ => ?_
  exact ⟨hct, hmt,
    (hft.wv_of_not_mem (by decide) (by decide) hz).trans bR,
    (hft.wv_of_not_mem (by decide) (by decide) hz).trans hb, ht,
    ((hfw.trans hfa).trans (arrays_work hfb (by decide))).trans (arrays_work hft (by decide)),
    ((((hkw.trans hkz).trans hka).trans hkb).trans hkt).mono (by decide)⟩

end VG.Proof.Dsa.X86_64
