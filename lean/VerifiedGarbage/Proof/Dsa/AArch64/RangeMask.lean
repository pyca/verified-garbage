module

public import VerifiedGarbage.Proof.Dsa.AArch64.RangeLow
public import VerifiedGarbage.Proof.Dsa.AArch64.RangeHead
public import VerifiedGarbage.Proof.Bignum.AArch64.Copy
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-! # Exact scalar range masks without secret-dependent branches -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

/-- The range mask is all ones exactly for 0 < X < N, or 1 < X < N.
The value and modulus can have leading zero limbs. -/
theorem rangeMask_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (aboveOne : Bool) :
    WP isa (Checks.rangeMask aboveOne) s fun t =>
      t.gpr .x15 = mask (decide ((if aboveOne then 1 else 0) < wv s.mem B (slot w aX) w ∧
        wv s.mem B (slot w aX) w < wv s.mem B (slot w aN) w)) ∧
      t.mem = s.mem ∧ Keep [.x3, .x4, .x7, .x9, .x11, .x12, .x14, .x15, .x16, .x17] s t := by
  have hx := Nat.le_trans (slot_le (w := w) (show aX < 8 by decide)) hZ
  have hn := Nat.le_trans (slot_le (w := w) (show aN < 8 by decide)) hZ
  unfold Checks.rangeMask seqs
  refine WP.seq (WP.mono (rangeHead_ok hg hZ)
    fun u ⟨hu12, hu16, hu17, hu14, hu7, huc, hum, hku⟩ => ?_)
  refine WP.seq (WP.mono (cmpLoop_ok (hg.scr.congr hku.wr) hu16 hu17 hu14 huc (by omega)
    hw' (by omega) (by omega)) fun v ⟨hvc, hvm, hkv⟩ => ?_)
  have hkuv := hku.trans hkv
  have hvs : v.mem = s.mem := hvm.trans hum
  have hgv : Good v B Z w minv :=
    ⟨hg.scr.congr hkuv.wr, (hkuv.gpr .x0 (by decide)).trans hg.x0, hvs ▸ hg.hdr⟩
  refine WP.seq (WP.mono (rangeLow_ok hgv hZ (by omega) ((hkv.gpr .x7 (by decide)).trans hu7)
    ((hkv.gpr .x12 (by decide)).trans hu12) aboveOne) fun z ⟨hz11, hz9, hz16, hz14, hzm, hkz⟩ => ?_)
  have hlow : z.gpr .x9 = 0 ↔ rangeLow aboveOne (word z.mem B (slot w aX)) = 0 := by rw [hz9, hzm]
  refine WP.seq (WP.mono (orWords_ok (hgv.scr.congr hkz.wr) hz16 hz14 hlow hw hw' (by omega))
    fun f ⟨hf9, hfm, hkf⟩ => ?_)
  rw [rangeLow_words (by omega) aboveOne, hzm, hvs] at hf9
  have hf11 : f.gpr .x11 = mask (decide (wv s.mem B (slot w aX) w < wv s.mem B (slot w aN) w)) :=
    (hkf.gpr .x11 (by decide)).trans (by rw [hz11, hvc, hum, Bool.not_not])
  have hfs : f.mem = s.mem := hfm.trans (hzm.trans hvs)
  have hkf' := ((hkuv.trans hkz).trans hkf)
  have he : (!decide (f.gpr .x9 = 0) &&
      decide (wv s.mem B (slot w aX) w < wv s.mem B (slot w aN) w)) =
      decide ((if aboveOne then 1 else 0) < wv s.mem B (slot w aX) w ∧
        wv s.mem B (slot w aX) w < wv s.mem B (slot w aN) w) := by
    rw [decide_eq_decide.mpr hf9, ← decide_not, ← Bool.decide_and]
    exact decide_eq_decide.mpr (by omega)
  change WP isa (.block _) f _
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.x3] (Q := fun g => g.gpr .x3 = f.gpr .x9 ∧ g.mem = f.mem) (by brun)
    (by decide) (by decide) (by decide +kernel)) fun g ⟨⟨hg3, hgm⟩, hkg⟩ => ?_
  refine WP.mono (zeroMask_ok g) fun l ⟨⟨hl15, hl4, _, hlm⟩, hkl⟩ => ?_
  have hl11 := (hkl.gpr .x11 (by decide)).trans ((hkg.gpr .x11 (by decide)).trans hf11)
  rw [hg3] at hl15
  refine WP.mono (WP.keep [.x15] (Q := fun t =>
    t.gpr .x15 = mask (decide ((if aboveOne then 1 else 0) < wv s.mem B (slot w aX) w ∧
      wv s.mem B (slot w aX) w < wv s.mem B (slot w aN) w)) ∧ t.mem = l.mem) ?_
    (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨ht, htm⟩, hkt⟩ =>
      ⟨ht, htm.trans (hlm.trans (hgm.trans hfs)), (((hkf'.trans hkg).trans hkl).trans hkt).mono (by decide)⟩
  brun [hl15, hl4, hl11, mask_true, mask_complement, mask_intersect, he]

end VG.Proof.Dsa.AArch64
