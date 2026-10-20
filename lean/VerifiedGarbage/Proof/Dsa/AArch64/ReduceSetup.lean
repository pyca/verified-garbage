module
public import VerifiedGarbage.Proof.Dsa.AArch64.Frame

import VerifiedGarbage.Proof.Dsa.AArch64.Prepare
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
import VerifiedGarbage.Proof.Dsa.AArch64.Setup
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Bignum.Math

/-! # Preparing the ordinary accumulator for streaming byte reduction -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

/-- Clearing an operand preserves the linked workspace and modulus. -/
theorem clear_mod_ok {s : State} {B : Addr} {Z o w wx m : Nat} {minv : BitVec 64}
    (hc : SubCtx s B Z o w wx minv) (hm : ModCtx s (off B o) (slot wx 8) wx minv m)
    (hw : 2 ≤ wx) (hw' : wx < 2 ^ 31) {j : Nat} (hj : j < 8) (hjn : j ≠ aN) :
    WP isa (Arithmetic.zero j) s fun t =>
      SubCtx t B Z o w wx minv ∧ ModCtx t (off B o) (slot wx 8) wx minv m ∧
      wv t.mem (off B o) (slot wx j) wx = 0 ∧
      Arrays (off B o) wx [j] s.mem t.mem ∧ Keep mmRegs s t := by
  refine WP.mono (zeroArr_ok hc.good (Nat.le_refl _) hw' hj)
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

/-- Reduction starts with ordinary zero and multiplier 256R, even for
composite moduli with zero high limbs. -/
theorem reduceSetup_ok (M : Mont) {s : State} {B : Addr} {Z o w wx m : Nat}
    {minv : BitVec 64} (hc : SubCtx s B Z o w wx minv)
    (hw : 2 ≤ wx) (hw48 : wx ≤ 48) (hm : 1 < m) (hodd : m % 2 = 1)
    (hn : wv s.mem (off B o) (slot wx aN) wx = m)
    (hinv : ((word s.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0) :
    WP isa (Arithmetic.reduceSetup M.mm) s fun t =>
      SubCtx t B Z o w wx minv ∧ ModCtx t (off B o) (slot wx 8) wx minv m ∧
      wv t.mem (off B o) (slot wx aXm) wx = 256 * 2 ^ (64 * wx) % m ∧
      wv t.mem (off B o) (slot wx aY) wx = 0 ∧
      wv t.mem (off B o) (slot wx aX) wx = 0 ∧
      Frm (off B o) (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  have hw' : wx < 2 ^ 31 := by omega
  have hz := hc.good.scr.nowrap
  unfold Arithmetic.reduceSetup seqs
  refine WP.seq (WP.mono (prepare_ok M hc hw hw48 hm hodd hn hinv)
    fun u ⟨hcu, hmu, huone, hur2, hfu, hku⟩ => ?_)
  refine WP.seq (WP.mono (small_ok hcu.good (Nat.le_refl _) hw hw' (by decide)
    (value := 256) (by decide)) fun v ⟨hgv, hv, hfv, hkv⟩ => ?_)
  have hcv := arrays_context hcu hfv (by decide) hkv
  have hmv : ModCtx v (off B o) (slot wx 8) wx minv m := ⟨hgv,
    (hfv.wv_of_not_mem (by decide) (by decide) hz).trans hmu.modulus, by
      rw [hfv.word0_of_not_mem (by decide) (by decide) hz (by omega)]; exact hmu.inverse⟩
  have vr2 := (hfv.wv_of_not_mem (show aR2 < 8 by decide) (by decide) hz).trans hur2
  refine WP.seq (WP.mono (mont_step M hmv (Nat.le_refl _) hw hw'
    (by unfold MmUse; decide) (by rw [vr2]; exact Nat.mod_lt _ (by omega)))
    fun a ⟨hma, hlt, ha, hfa, hka⟩ => ?_)
  rw [hv, vr2, show 128 * wx = 64 * wx + 64 * wx by omega, Nat.pow_add] at ha
  have hscale := VG.Proof.Dsa.mont_scale (coprime_pow2 hodd (64 * wx)) ha
  rw [Nat.mod_eq_of_lt hlt] at hscale
  have hca := arrays_context hcv hfa (by decide) hka
  have hfw := hfu.trans (arrays_work hfv (by decide))
  have hkw := (hku.trans hkv).mono (show ∀ r ∈ mmRegs ++ mmRegs, r ∈ mmRegs by decide)
  refine WP.seq (WP.mono (clear_mod_ok hca hma hw hw' (by decide) (by decide))
    fun b ⟨hcb, hmb, hb, hfb, hkb⟩ => ?_)
  have bR := (hfb.wv_of_not_mem (show aXm < 8 by decide) (by decide) hz).trans hscale
  refine WP.mono (clear_mod_ok hcb hmb hw hw' (by decide) (by decide))
    fun t ⟨hct, hmt, ht, hft, hkt⟩ => ?_
  exact ⟨hct, hmt,
    (hft.wv_of_not_mem (by decide) (by decide) hz).trans bR,
    (hft.wv_of_not_mem (by decide) (by decide) hz).trans hb, ht,
    ((hfw.trans (arrays_work hfa (by decide))).trans (arrays_work hfb (by decide))).trans (arrays_work hft (by decide)),
    (((hkw.trans hka).trans hkb).trans hkt).mono (by decide)⟩

end VG.Proof.Dsa.AArch64
