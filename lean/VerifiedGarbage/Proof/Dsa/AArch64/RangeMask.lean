module
public import Mathlib.Data.Int.GCD
public import VerifiedGarbage.Impl.Dsa.AArch64.Checks
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public import VerifiedGarbage.Proof.Framework.Contract

import VerifiedGarbage.Proof.Dsa.AArch64.LowerScan
import VerifiedGarbage.Proof.Dsa.AArch64.ZeroMask
import VerifiedGarbage.Proof.Dsa.AArch64.Masks
import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
import VerifiedGarbage.Proof.Bignum.AArch64.Copy
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! # Exact scalar and element range checks -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem rangeMask_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (aboveOne : Bool) :
    WP isa (Checks.rangeMask aboveOne) s fun t =>
      t.gpr .x3 = mask (decide ((if aboveOne then 1 else 0) < wv s.mem B (slot w aX) w ∧
        wv s.mem B (slot w aX) w < wv s.mem B (slot w aN) w)) ∧
      t.mem = s.mem ∧ Keep mmRegs s t := by
  have hx := Nat.le_trans (slot_le (w := w) (show aX < 8 by decide)) hZ
  have hn := Nat.le_trans (slot_le (w := w) (show aN < 8 by decide)) hZ
  unfold Checks.rangeMask seqs
  refine WP.seq (WP.mono (lowerScan_ok hg hZ hw hw' aboveOne) fun u ⟨hu15, hum, hku⟩ => ?_)
  have hgu : Good u B Z w minv := ⟨hg.scr.congr hku.wr, (hku.gpr .x0 (by decide)).trans hg.x0, hum ▸ hg.hdr⟩
  refine WP.seq (WP.mono (WP.keep [.x16, .x17, .x14, .x7, .x3] (Q := fun v =>
    v.gpr .x16 = off B (slot w aX) ∧ v.gpr .x17 = off B (slot w aN) ∧
    v.gpr .x14 = BitVec.ofNat 64 w ∧ v.c = true ∧ v.mem = u.mem)
    (by brun [hgu.x0, hdr_enc (show sArr aX < 32 by decide), hdr_enc (show sArr aN < 32 by decide),
      hdr_enc (show sW < 32 by decide), hgu.hdr.harr aX (by decide), hgu.hdr.harr aN (by decide), hgu.hdr.hw,
      hgu.ld hZ (show sArr aX < 32 by decide), hgu.ld hZ (show sArr aN < 32 by decide), hgu.ld hZ (show sW < 32 by decide)])
    rfl rfl rfl) fun v ⟨⟨hv16, hv17, hv14, hvc, hvm⟩, hkv⟩ => ?_)
  have hk : Keep mmRegs s v := (hku.trans hkv).mono (by decide)
  refine WP.seq (WP.mono (cmpLoop_ok (hg.scr.congr hk.wr) hv16 hv17 hv14 hvc (by omega) hw' (by omega) (by omega))
    fun z ⟨hzc, hzm, hkz⟩ => ?_)
  rw [hvm, hum] at hzc
  refine WP.seq (WP.mono (WP.keep [.x3, .x4, .x5] (Q := fun f =>
    f.gpr .x5 = mask (decide (wv s.mem B (slot w aX) w < wv s.mem B (slot w aN) w)) ∧ f.mem = z.mem)
    ?_ rfl rfl rfl) fun f ⟨⟨hf5, hfm⟩, hkf⟩ => ?_)
  · brun [hzc]
    generalize decide (wv s.mem B (slot w aX) w < wv s.mem B (slot w aN) w) = b
    cases b <;> rfl
  have hf15 : f.gpr .x15 = 0 ↔ wv s.mem B (slot w aX) w ≤ (if aboveOne then 1 else 0) := by
    rw [hkf.gpr .x15 (by decide), hkz.gpr .x15 (by decide), hkv.gpr .x15 (by decide)]
    exact hu15
  change WP isa (.block _) f _
  rw [WP.block_append_iff]
  refine WP.mono (zeroMask_ok .x15 true) fun l ⟨hl3, hlm, hkl⟩ => ?_
  have hl5 := (hkl.gpr .x5 (by decide)).trans hf5
  have he : (!decide (f.gpr .x15 = 0) && decide (wv s.mem B (slot w aX) w < wv s.mem B (slot w aN) w)) =
      decide ((if aboveOne then 1 else 0) < wv s.mem B (slot w aX) w ∧ wv s.mem B (slot w aX) w < wv s.mem B (slot w aN) w) := by
    rw [decide_eq_decide.mpr hf15, ← decide_not, ← Bool.decide_and]
    exact decide_eq_decide.mpr (by omega)
  refine WP.mono (WP.keep [.x3] (Q := fun t =>
    t.gpr .x3 = mask (decide ((if aboveOne then 1 else 0) < wv s.mem B (slot w aX) w ∧
      wv s.mem B (slot w aX) w < wv s.mem B (slot w aN) w)) ∧ t.mem = l.mem)
    (by brun [hl3, hl5, mask_intersect, he]) rfl rfl rfl) fun t ⟨⟨ht, htm⟩, hkt⟩ => ?_
  have hkz' : Keep mmRegs s z := (hk.trans hkz).mono (by decide)
  have hkf' : Keep mmRegs s f := (hkz'.trans hkf).mono (by decide)
  exact ⟨ht, htm.trans (hlm.trans (hfm.trans (hzm.trans (hvm.trans hum)))), ((hkf'.trans hkl).trans hkt).mono (by decide)⟩

end VG.Proof.Dsa.AArch64
