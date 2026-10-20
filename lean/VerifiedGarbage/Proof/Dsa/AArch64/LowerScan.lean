module
public import Mathlib.Data.Int.GCD
public import VerifiedGarbage.Impl.Dsa.AArch64.Checks
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public import VerifiedGarbage.Proof.Framework.Contract

import VerifiedGarbage.Proof.Dsa.AArch64.RangeLow
import VerifiedGarbage.Proof.Dsa.AArch64.OrWords
import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! # Rejecting zero and one with a fixed-length limb scan -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem lowerScan_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (aboveOne : Bool) :
    WP isa (Checks.lowerScan aboveOne) s fun t =>
      (t.gpr .x15 = 0 ↔ wv s.mem B (slot w aX) w ≤ (if aboveOne then 1 else 0)) ∧
      t.mem = s.mem ∧ Keep mmRegs s t := by
  have hx := Nat.le_trans (slot_le (w := w) (show aX < 8 by decide)) hZ
  unfold Checks.lowerScan seqs
  refine WP.seq (WP.mono (WP.keep [.x12, .x16] (Q := fun u =>
    u.gpr .x12 = BitVec.ofNat 64 w ∧ u.gpr .x16 = off B (slot w aX) ∧ u.mem = s.mem)
    (by brun [hg.x0, hdr_enc (show sW < 32 by decide), hdr_enc (show sArr aX < 32 by decide),
      hg.hdr.hw, hg.hdr.harr aX (by decide), hg.ld hZ (show sW < 32 by decide), hg.ld hZ (show sArr aX < 32 by decide)])
    rfl rfl rfl) fun u ⟨⟨hu12, hu16, hum⟩, hku⟩ => ?_)
  refine WP.seq (WP.mono (rangeLow_ok (hg.scr.congr hku.wr) hu16 (by omega) aboveOne)
    fun v ⟨hv15, hvm, hkv⟩ => ?_)
  have hv12 := (hkv.gpr .x12 (by decide)).trans hu12
  have hv16 := (hkv.gpr .x16 (by decide)).trans hu16
  have hsub : BitVec.ofNat 64 w - (1#64) = BitVec.ofNat 64 (w - 1) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    simp only [Nat.mod_eq_of_lt (show 1 < 2 ^ 64 by decide)]
    omega
  refine WP.seq (WP.mono (WP.keep [.x16, .x14] (Q := fun z =>
    z.gpr .x16 = off B (slot w aX + 8) ∧ z.gpr .x14 = BitVec.ofNat 64 (w - 1) ∧ z.mem = v.mem)
    (by brun [hv16, hv12, hsub]) rfl rfl rfl) fun z ⟨⟨hz16, hz14, hzm⟩, hkz⟩ => ?_)
  have hk : Keep mmRegs s z := ((hku.trans hkv).trans hkz).mono (by decide)
  have hz15 : z.gpr .x15 = 0 ↔ rangeLow aboveOne (word s.mem B (slot w aX)) = 0 := by
    rw [hkz.gpr .x15 (by decide), hv15, hum]
  refine WP.mono (orWords_ok (hg.scr.congr hk.wr) hz16 hz14 hz15 (by omega) (by omega) (by omega))
    fun t ⟨ht, htm, hkt⟩ => ?_
  have hm : z.mem = s.mem := hzm.trans (hvm.trans hum)
  rw [hm] at ht
  have he : (∀ i < w - 1, word s.mem B (slot w aX + 8 + 8 * i) = 0) ↔
      ∀ i, 1 ≤ i → i < w → word s.mem B (slot w aX + 8 * i) = 0 := by
    constructor
    · intro h i hi hiw
      have hh := h (i - 1) (by omega)
      convert hh using 2 <;> omega
    · intro h i hi
      have hh := h (i + 1) (by omega) (by omega)
      convert hh using 2 <;> omega
  rw [he, rangeLow_words (by omega) aboveOne] at ht
  exact ⟨ht, htm.trans hm, (hk.trans hkt).mono (by decide)⟩

end VG.Proof.Dsa.AArch64
