module
public import VerifiedGarbage.Impl.Bignum.AArch64.ProductEight
public import VerifiedGarbage.Proof.Bignum.AArch64.MontMul
public import VerifiedGarbage.Proof.Ed25519.Word64

import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLayout
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRaw
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCorrect
import VerifiedGarbage.Proof.Bignum.AArch64.FastFinish
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcRestore
import VerifiedGarbage.Proof.Bignum.AArch64.SquareFinish
import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcSave

@[expose] public section

namespace VG.Proof.Bignum.AArch64.ProductMont
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.Bignum.AArch64 VG.Proof.Ed25519.Word64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Bignum.AArch64.BlockedRedc

theorem multiply_ok {s : State} {B : Addr} {Z w : Nat} {minv : Word}
    (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (hH : Hdr s.mem B w minv)
    (hZ : slot w 8 ≤ Z) (hw16 : 16 ≤ w) (hw : w < 2 ^ 31) (hmod : w % 8 = 0)
    {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8) (ho1 : o ≠ aAcc) (ho2 : o ≠ aTmp)
    (hoN : o ≠ aN) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp)
    (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hB : wv s.mem B (slot w b) w < wv s.mem B (slot w aN) w) :
    WP isa (VG.Impl.Bignum.AArch64.ProductEight.multiply o a b) s fun t =>
      wv t.mem B (slot w o) w < wv s.mem B (slot w aN) w ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s.mem B (slot w aN) w =
        wv s.mem B (slot w a) w * wv s.mem B (slot w b) w % wv s.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hs.nowrap
  have hNs := slot_le (w := w) (show aN < 8 by decide)
  have hsep : slot w aN + 8 * (w + 2) ≤ slot w aAcc := by unfold slot aN aAcc; omega_arith
  have hmpos : 0 < wv s.mem B (slot w aN) w := by omega_arith
  have hSpillN : slot w o + 88 ≤ slot w aN ∨ slot w aN + 8 * (w + 2) ≤ slot w o := by
    have := slot_sep (w := w) hoN
    omega_arith
  have hSpillScratch : slot w o + 88 ≤ slot w aAcc + 16 ∨
      slot w aAcc + 16 + 8 * (2 * w + 2) ≤ slot w o := by
    have := slot_sep (w := w) ho1
    have := slot_sep (w := w) ho2
    unfold slot aAcc aTmp at *
    omega_arith
  have hOutBound := slot_le (w := w) ho
  unfold VG.Impl.Bignum.AArch64.ProductEight.multiply
  refine WP.seq (WP.mono (ProductEight.raw_width_ok hs h0 hH hZ hw16 hw hmod ha hb ha1 ha2 hb1 hb2)
    fun u ⟨huRaw, huOut, hu8, _, hu12, _, hu7, ku⟩ => ?_)
  have hHU := (Square.scratch_arrays huOut).hdr hH
  refine WP.seq (WP.mono (saves_ok (hs.congr ku.wr) ((ku.gpr .x0 (by decide)).trans h0)
    hHU hZ ho hw16) fun v ⟨hSaved, hvOut, kv⟩ => ?_)
  have kuv := ku.trans kv
  have hHV := (spill_arrays hw16 hvOut).hdr hHU
  have hN0 : word v.mem B (slot w aN) = word s.mem B (slot w aN) :=
    (hvOut.word (by omega_arith) (by omega_arith)).trans (huOut.word (by omega_arith) (by omega_arith))
  have hNV : wv v.mem B (slot w aN) w = wv s.mem B (slot w aN) w :=
    (hvOut.wv (by omega_arith) (by omega_arith)).trans (huOut.wv (by omega_arith) (by omega_arith))
  have hRawV := (hvOut.wv (d := slot w aAcc + 16) (k := 2 * w) (by omega_arith)
    (by have := slot_le (w := w) (show aTmp < 8 by decide); unfold slot aAcc aTmp at *; omega_arith)).trans huRaw
  refine WP.seq (WP.mono (redc_layout_ok (hs.congr kuv.wr) ((kuv.gpr .x0 (by decide)).trans h0)
    hHV hZ ((kv.gpr .x8 (by decide)).trans hu8) ((kv.gpr .x12 (by decide)).trans hu12)
    ((kv.gpr .x7 (by decide)).trans hu7) hw16 (by omega_arith) hmod)
    fun r ⟨hrValue, hrOut, hr8, hr10, hr12, hr7, kr⟩ => ?_)
  have kuvr := kuv.trans kr
  have invV : ((word v.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 := by
    rw [hN0]
    exact hinv
  obtain ⟨q, hq, heq⟩ := hrValue invV
  rewrite [hRawV, hNV] at heq
  have hNR : wv r.mem B (slot w aN) w = wv s.mem B (slot w aN) w :=
    (hrOut.wv (by omega_arith) (by omega_arith)).trans hNV
  have hHR := (Square.scratch_arrays hrOut).hdr hHV
  have hSavedR : ∀ i < 11, word r.mem B (slot w o + 8 * i) =
      u.gpr VG.Impl.Bignum.AArch64.BlockedRedc.saved[i]! :=
    fun i hi => (hrOut.word (by omega_arith) (by omega_arith)).trans (hSaved i hi)
  have hFrameV : Arrays B w [aAcc, aTmp, o] s.mem v.mem :=
    ((Square.scratch_arrays huOut).mono (by simp)).trans ((spill_arrays hw16 hvOut).mono (by simp))
  have hFrameR : Arrays B w [aAcc, aTmp, o] s.mem r.mem :=
    hFrameV.trans ((Square.scratch_arrays hrOut).mono (by simp))
  apply WP.seq
  apply WP.block_append
  refine WP.mono (restores_ok (hs.congr kuvr.wr) ((kuvr.gpr .x0 (by decide)).trans h0)
    hHR hZ ho hw16 hSavedR) fun d ⟨hRestored, hdm, kd⟩ => ?_
  have hFrameD : Arrays B w [aAcc, aTmp, o] s.mem d.mem := by
    intro x hx
    exact (congrArg (fun m : Mem => m x) hdm).trans (hFrameR x hx)
  have hHD := hFrameD.hdr hH
  have kSaved : ∀ r ∈ VG.Impl.Bignum.AArch64.BlockedRedc.saved, r ∉ mmRegs := by decide
  have kPre : Keep mmRegs s d := keep_restored ((kuvr.trans kd).mono (by decide))
    (fun r hr => (hRestored r hr).trans (ku.gpr r (kSaved r hr)))
  have hND := (congrArg (fun m : Mem => wv m B (slot w aN) w) hdm).trans hNR
  have hProduct : wv s.mem B (slot w a) w * wv s.mem B (slot w b) w <
      wv s.mem B (slot w aN) w * 2 ^ (64 * w) := by
    have hp := Nat.mul_lt_mul'' hB (wv_lt s.mem B (slot w a) w)
    exact (Nat.mul_comm _ _) ▸ hp
  have hTR : wv r.mem B (slot w aTmp) (w + 2) < 2 * wv s.mem B (slot w aN) w :=
    Square.redc_lt hmpos hq hProduct heq
  have hTD : wv d.mem B (slot w aTmp) (w + 2) < 2 * wv s.mem B (slot w aN) w := by
    rw [hdm]
    exact hTR
  refine WP.mono (Square.finishBases_ok (hs.congr kPre.wr)
    ((kPre.gpr .x0 (by decide)).trans h0) hHD hZ ho) fun c ⟨⟨hc5, hc6, hcm⟩, kc⟩ => ?_
  have kAll := kPre.trans kc
  refine WP.mono (FastFinish.finish_ok (hs.congr kAll.wr) hZ
    (((kd.trans kc).gpr .x8 (by decide)).trans hr8)
    (((kd.trans kc).gpr .x10 (by decide)).trans hr10) hc6 hc5
    (((kd.trans kc).gpr .x12 (by decide)).trans hr12)
    (((kd.trans kc).gpr .x7 (by decide)).trans hr7)
    (by omega_arith) hw (by omega_arith) ho ho1 ho2 (by rw [hcm, hND]; exact hmpos)
    (by rw [hcm, hND]; exact hTD)) fun t ⟨hRes, hOut, kt⟩ => ?_
  rewrite [hcm, hdm, hNR] at hRes
  refine ⟨?_, ?_, ?_, (kAll.trans kt).mono (by decide)⟩
  · rw [hRes]
    exact Nat.mod_lt _ hmpos
  · rw [hRes, Nat.mod_mul_mod, Nat.mul_comm, heq, Nat.add_mul_mod_self_right]
  · have hOut' := hOut.mono (js' := [aAcc, aTmp, o]) (by simp)
    have hFrameC : Arrays B w [aAcc, aTmp, o] s.mem c.mem := by
      intro x hx
      exact (congrArg (fun m : Mem => m x) hcm).trans (hFrameD x hx)
    exact hFrameC.trans hOut'

end VG.Proof.Bignum.AArch64.ProductMont
