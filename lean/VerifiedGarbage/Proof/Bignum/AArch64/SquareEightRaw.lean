module

import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightDiagonal
public import VerifiedGarbage.Proof.Bignum.AArch64.MontMul
public import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRows
public import VerifiedGarbage.Impl.Bignum.AArch64.SquareEightRaw
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareMath
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightRows
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRaw
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightSetup
import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
import VerifiedGarbage.Proof.Bignum.AArch64.SquareRaw
import VerifiedGarbage.Proof.Bignum.AArch64.WideZero
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Block

@[expose] public section
namespace VG.Proof.Bignum.AArch64.SquareEight
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

open VG.Proof.Bignum.AArch64.ProductEight (productBase saves_ok start_ok restores_ok saved_lane_exists savedLanes)

/-- The unreduced triangle before doubling and adding the diagonal. -/
def triangle (a : Nat) : Prog isa :=
 .seq (.block (Square.squareSetup a))
 (.seq VG.Impl.Bignum.AArch64.WideLoops.zero
 (.seq (.block (VG.Impl.Bignum.AArch64.ProductEight.saves ++ [ldh .x8 (sArr a), .lsr .x .x12 .x12 3]))
 (.seq (SquareEightRaw.rows a) (.block (VG.Impl.Bignum.AArch64.ProductEight.restores ++ Square.squareSetup a)))))

/-- Exact triangular product in the existing scratch arrays, with every saved
scalar register restored before returning. No arithmetic input bound is needed. -/
theorem triangle_ok {s : State} {B : Addr} {Z k : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (hH : Hdr s.mem B (8 * k) minv)
    (hZ : slot (8 * k) 8 ≤ Z) (hk : 0 < k) (hk' : k < 2 ^ 56)
    {a : Nat} (ha : a < 8)
    (ha1 : a ≠ Public.aAcc) (ha2 : a ≠ Public.aTmp) :
    WP isa (triangle a) s fun t =>
      wv t.mem B (productBase k) (16 * k + 2) =
        Square.crossValue s.mem B (slot (8*k) a) (8*k) ∧
      Outside B (productBase k) (8 * (16 * k + 2)) s.mem t.mem ∧
      t.gpr .x8 = off B (productBase k) ∧ t.gpr .x9 = off B (slot (8*k) a) ∧ t.gpr .x10 = off B (slot (8 * k) Public.aN) ∧
      t.gpr .x12 = BitVec.ofNat 64 (8 * k) ∧ t.gpr .x15 = minv ∧ t.gpr .x7 = 0 ∧
      Keep mmRegs s t := by
  have hn := hs.nowrap
  have hP : productBase k + 8 * (16 * k + 2) ≤ Z := by
    unfold productBase slot Public.aAcc at *
    omega
  have sep : ∀ j < 8, j ≠ Public.aAcc → j ≠ Public.aTmp →
      slot (8 * k) j + 64 * k ≤ productBase k ∨
        productBase k + 8 * (16 * k + 2) ≤ slot (8 * k) j := by
    intro j hj hj1 hj2
    have := slot_sep (w := 8 * k) hj1
    have := slot_sep (w := 8 * k) hj2
    unfold productBase slot Public.aAcc Public.aTmp at *
    omega
  unfold triangle
  refine WP.seq (WP.mono (Square.squareSetup_ok hs h0 hH hZ ha)
    fun u ⟨⟨hu8, _, _, hu12, _, hu7, hum⟩, ku⟩ => ?_)
  refine WP.seq (WP.mono (WideLoops.zero_ok (hs.congr ku.wr) hu8 hu7 hu12 hP hk hk')
    fun v ⟨hv0, hvo, kv⟩ => ?_)
  have ksv := ku.trans kv
  have hvs : Outside B (productBase k) (8 * (16 * k + 2)) s.mem v.mem := by
    intro x hx
    exact (hvo x hx).trans (congrArg (fun m : Mem => m x) hum)
  have hHv : Hdr v.mem B (8 * k) minv :=
    (Square.scratch_arrays (by simpa only [productBase, show 2 * (8 * k) = 16 * k by omega] using hvs)).hdr hH
  refine WP.seq (WP.block_append ?_)
  refine WP.mono (saves_ok v) fun v0 ⟨⟨hv0m, lanes⟩, ks⟩ => ?_
  refine WP.mono (start_ok (hs.congr (ks.wr.trans ksv.wr))
    ((ks.gpr .x0 (by decide)).trans ((ksv.gpr .x0 (by decide)).trans h0))
    (hv0m ▸ hHv) hZ ha hk'
    ((ks.gpr .x12 (by decide)).trans ((kv.gpr .x12 (by decide)).trans hu12)))
    fun v1 ⟨⟨hv18, hv112, hv1m, hv1v⟩, kstart⟩ => ?_
  have kpre := (ksv.trans ks).trans kstart
  have hv1zero : wv v1.mem B (productBase k) (16 * k + 2) = 0 := by
    rw [hv1m, hv0m]
    exact hv0
  have hv1H : Hdr v1.mem B (8 * k) minv := by rw [hv1m, hv0m]; exact hHv
  refine WP.seq (WP.mono (rows_ok (hs.congr kpre.wr)
    ((kpre.gpr .x0 (by decide)).trans h0)
    ((kstart.gpr .x7 (by decide)).trans ((ks.gpr .x7 (by decide)).trans
      ((kv.gpr .x7 (by decide)).trans hu7))) hv1H hZ hv18 hv112 ha hk hk'
    (sep a ha ha1 ha2) hv1zero)
    fun v2 ⟨hr, hvec⟩ => ?_)
  apply WP.block_append
  refine WP.mono (restores_ok v2) fun v3 ⟨⟨hv3m, restored⟩, kr⟩ => ?_
  have kv3 := (kpre.trans hr.keep).trans kr
  have hvs3 : Outside B (productBase k) (8 * (16 * k + 2)) s.mem v3.mem := by
    have hvs1 : Outside B (productBase k) (8 * (16 * k + 2)) s.mem v1.mem := by
      intro x hx
      exact (congrArg (fun m : Mem => m x) (hv1m.trans hv0m)).trans (hvs x hx)
    intro x hx
    exact (congrArg (fun m : Mem => m x) hv3m).trans ((hvs1.trans hr.frame) x hx)
  have hHv3 : Hdr v3.mem B (8 * k) minv :=
    (Square.scratch_arrays (by simpa only [productBase, show 2 * (8 * k) = 16 * k by omega] using hvs3)).hdr hH
  refine WP.mono (Square.squareSetup_ok (hs.congr kv3.wr)
    ((kv3.gpr .x0 (by decide)).trans h0) hHv3 hZ ha)
    fun t ⟨⟨ht8, ht9, ht10, ht12, ht15, ht7, htm⟩, kt⟩ => ?_
  have kout := kv3.trans kt
  refine ⟨?_, ?_, ht8, ht9, ht10, ht12, ht15, ht7, ?_⟩
  · rw [htm, hv3m, hr.value]
    apply Square.crossValue_congr
    intro j hj
    rw [hv1m, hv0m]
    exact hvs.word (by have := sep a ha ha1 ha2; omega) (by
      have := slot_le (w := 8*k) ha
      omega)
  · intro x hx
    exact (congrArg (fun m : Mem => m x) htm).trans (hvs3 x hx)
  · refine ⟨?_, kout.rd, kout.wr, kout.sp, kout.vcs⟩
    intro r hrmm
    by_cases hrs : r ∈ VG.Impl.Bignum.AArch64.ProductEight.regs
    · obtain ⟨vreg, hvreg⟩ := saved_lane_exists r hrs
      have hkr := restored (r, vreg, 0) hvreg
      have hvsaved := lanes (r, vreg, 0) hvreg
      have hLane : laneOf v2 vreg 0 = laneOf v0 vreg 0 := by
        unfold laneOf
        rw [hvec, hv1v]
      have hrv : v.gpr r = s.gpr r := ksv.gpr r (by
        intro h
        exact hrmm (by exact (show ∀ r ∈ [.x8, .x9, .x10, .x12, .x15, .x7] ++ [.x14, .x16], r ∈ mmRegs by decide) r h))
      exact (kt.gpr r (by intro h; exact hrmm ((show ∀ r ∈ [.x8, .x9, .x10, .x12, .x15, .x7], r ∈ mmRegs by decide) r h))).trans
        (hkr.trans (hLane.trans (hvsaved.trans hrv)))
    · exact kout.gpr r (by
        intro h
        have hsub : ∀ r ∈
            ((([.x8, .x9, .x10, .x12, .x15, .x7] ++ [.x14, .x16]) ++ []) ++ [.x8, .x12]) ++
              rawRegs ++ VG.Impl.Bignum.AArch64.ProductEight.regs ++ [.x8, .x9, .x10, .x12, .x15, .x7],
            r ∈ mmRegs ∨ r ∈ VG.Impl.Bignum.AArch64.ProductEight.regs := by decide
        exact (hsub r h).elim hrmm hrs)


/-- Complete scheduled square, including diagonal accumulation and ABI
restoration, under the existing RSA scratch layout. -/
theorem raw_ok {s : State} {B : Addr} {Z k : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (hH : Hdr s.mem B (8*k) minv)
    (hZ : slot (8*k) 8 ≤ Z) (hk : 0 < k) (hk' : k < 2 ^ 56)
    {a : Nat} (ha : a < 8) (ha1 : a ≠ Public.aAcc) (ha2 : a ≠ Public.aTmp) :
    WP isa (VG.Impl.Bignum.AArch64.SquareEightRaw.raw a) s fun t =>
      wv t.mem B (productBase k) (16*k) =
        wv s.mem B (slot (8*k) a) (8*k) * wv s.mem B (slot (8*k) a) (8*k) ∧
      Outside B (productBase k) (8*(16*k+2)) s.mem t.mem ∧
      t.gpr .x8 = off B (productBase k) ∧ t.gpr .x10 = off B (slot (8*k) Public.aN) ∧
      t.gpr .x12 = BitVec.ofNat 64 (8*k) ∧ t.gpr .x15 = minv ∧ t.gpr .x7 = 0 ∧ Keep mmRegs s t := by
  have hn := hs.nowrap
  have hP : productBase k+8*(16*k+2) ≤ Z := by
    unfold productBase slot Public.aAcc at *
    omega
  have hA : slot (8*k) a+64*k ≤ Z := by
    have := slot_le (w := 8*k) ha
    omega
  have sep : slot (8*k) a+64*k ≤ productBase k ∨
      productBase k+8*(16*k+2) ≤ slot (8*k) a := by
    have := slot_sep (w := 8*k) ha1
    have := slot_sep (w := 8*k) ha2
    unfold productBase slot Public.aAcc Public.aTmp at *
    omega
  have hp : WP isa (.seq (triangle a) VG.Impl.Bignum.AArch64.WideLoops.diagonal) s (fun t =>
      wv t.mem B (productBase k) (16*k) =
        wv s.mem B (slot (8*k) a) (8*k) * wv s.mem B (slot (8*k) a) (8*k) ∧
      Outside B (productBase k) (8*(16*k+2)) s.mem t.mem ∧
      t.gpr .x8 = off B (productBase k) ∧ t.gpr .x10 = off B (slot (8*k) Public.aN) ∧
      t.gpr .x12 = BitVec.ofNat 64 (8*k) ∧ t.gpr .x15 = minv ∧ t.gpr .x7 = 0 ∧ Keep mmRegs s t) :=
    WP.seq (WP.mono (triangle_ok hs h0 hH hZ hk hk' ha ha1 ha2)
      (fun v ⟨hv, ho, h8, h9, h10, h12, h15, h7, kv⟩ => by
        have hcross : Square.crossValue v.mem B (slot (8*k) a) (8*k) =
            Square.crossValue s.mem B (slot (8*k) a) (8*k) := by
          apply Square.crossValue_congr
          intro j hj
          exact ho.word (by omega) (by omega)
        have hread := ho.wv (d := slot (8*k) a) (k := 8*k) (by omega) (by omega)
        exact WP.mono (diagonal_finish_ok (hs.congr kv.wr) h8 h9 h12 h7 hk hk' hP hA sep
          (hv.trans hcross.symm)) fun t ⟨ht, hto, kt⟩ =>
            ⟨by simpa only [hread] using ht, ho.trans hto,
              (kt.gpr _ (by decide)).trans h8, (kt.gpr _ (by decide)).trans h10,
              (kt.gpr _ (by decide)).trans h12, (kt.gpr _ (by decide)).trans h15,
              (kt.gpr _ (by decide)).trans h7, (kv.trans kt).mono (by decide)⟩))
  unfold VG.Impl.Bignum.AArch64.SquareEightRaw.raw
  refine WP.seq (WP.mono (WP.seq_iff.mp (WP.assoc hp)) fun _ h => ?_)
  refine WP.seq (WP.mono (WP.seq_iff.mp (WP.assoc h)) fun _ h => ?_)
  refine WP.seq (WP.mono (WP.seq_iff.mp (WP.assoc h)) fun _ h => ?_)
  exact WP.assoc h

theorem raw_width_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (hH : Hdr s.mem B w minv)
    (hZ : slot w 8 ≤ Z) (hw : 16 ≤ w) (hw' : w < 2 ^ 31) (hmod : w % 8 = 0)
    {a : Nat} (ha : a < 8) (ha1 : a ≠ Public.aAcc) (ha2 : a ≠ Public.aTmp) :
    WP isa (VG.Impl.Bignum.AArch64.SquareEightRaw.raw a) s fun t =>
      wv t.mem B (slot w Public.aAcc+16) (2*w) =
        wv s.mem B (slot w a) w * wv s.mem B (slot w a) w ∧
      Outside B (slot w Public.aAcc+16) (8*(2*w+2)) s.mem t.mem ∧
      t.gpr .x8 = off B (slot w Public.aAcc+16) ∧ t.gpr .x10 = off B (slot w Public.aN) ∧
      t.gpr .x12 = BitVec.ofNat 64 w ∧ t.gpr .x15 = minv ∧ t.gpr .x7 = 0 ∧ Keep mmRegs s t := by
  have he : w = 8*(w/8) := by omega
  have hH' : Hdr s.mem B (8*(w/8)) minv := he ▸ hH
  have hZ' : slot (8*(w/8)) 8 ≤ Z := he ▸ hZ
  have hlen : 16*(w/8) = 2*w := by omega
  have hp := raw_ok hs h0 hH' hZ' (by omega) (by omega) ha ha1 ha2
  simpa only [productBase, ← he, hlen] using hp

end VG.Proof.Bignum.AArch64.SquareEight
