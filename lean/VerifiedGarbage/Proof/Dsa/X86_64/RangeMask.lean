module
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Impl.Dsa.X86_64.Checks
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont

import VerifiedGarbage.Proof.Dsa.X86_64.RangeLow
import VerifiedGarbage.Proof.Dsa.X86_64.RangeHead
import VerifiedGarbage.Proof.Bignum.X86_64.Cmp
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Dsa.X86_64.OrWords
import VerifiedGarbage.Proof.Dsa.X86_64.Masks
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks

/-! # Exact scalar range masks without secret-dependent branches -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- The range mask is all ones exactly for 0 < X < N, or 1 < X < N.
The value and modulus can have leading zero limbs. -/
theorem rangeMask_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (aboveOne : Bool) :
    WP isa (Checks.rangeMask aboveOne) s fun t =>
      t.gpr .rax = mask (decide ((if aboveOne then 1 else 0) < wv s.mem B (slot w aX) w ∧
        wv s.mem B (slot w aX) w < wv s.mem B (slot w aN) w)) ∧
      t.mem = s.mem ∧ Keep [.rax, .r12, .rbx, .r10, .rbp, .r14, .r15] s t := by
  have hx := Nat.le_trans (slot_le (w := w) (show aX < 8 by decide)) hZ
  have hn := Nat.le_trans (slot_le (w := w) (show aN < 8 by decide)) hZ
  unfold Checks.rangeMask seqs
  refine WP.seq (WP.mono (rangeHead_ok hg hZ)
    fun u ⟨hu12, hubx, hu10, hubp, hum, hku⟩ => ?_)
  refine WP.seq (WP.mono (cmpLoop_ok (hg.scr.congr hku.2.2) hubx hu10 hu12 hubp (by omega)
    hw' (by omega) (by omega)) fun v ⟨hvbp, hvm, hkv⟩ => ?_)
  have hkuv := hku.trans hkv
  have hvbx := (hkv.gpr (show Reg.rbx ∉ [Reg.rax, Reg.rbp, Reg.r14] by decide)).trans hubx
  have hv12 := (hkv.gpr (show Reg.r12 ∉ [Reg.rax, Reg.rbp, Reg.r14] by decide)).trans hu12
  rw [hum] at hvbp
  refine WP.seq (WP.mono (rangeLow_ok (hg.scr.congr hkuv.2.2) hvbx (by omega) aboveOne)
    fun z ⟨hz15, hzm, hkz⟩ => ?_)
  have hzbx := (hkz.gpr (show Reg.rbx ∉ [Reg.r15] by decide)).trans hvbx
  have hz12 := (hkz.gpr (show Reg.r12 ∉ [Reg.r15] by decide)).trans hv12
  have hlow : z.gpr .r15 = 0 ↔ rangeLow aboveOne (word z.mem B (slot w aX)) = 0 := by rw [hz15, hzm]
  refine WP.seq (WP.mono (orWords_ok (hg.scr.congr (hkuv.trans hkz).2.2) hzbx hz12 hlow hw hw'
    (by omega)) fun f ⟨hf15, hfm, hkf⟩ => ?_)
  rw [rangeLow_words (by omega) aboveOne, hzm, hvm, hum] at hf15
  have hfbp := (hkf.gpr (show Reg.rbp ∉ [Reg.rax, Reg.r15, Reg.r14] by decide)).trans
    ((hkz.gpr (show Reg.rbp ∉ [Reg.r15] by decide)).trans hvbp)
  refine WP.mono (WP.keep [.rax, .r15] (Q := fun t =>
    t.gpr .rax = mask (decide ((if aboveOne then 1 else 0) < wv s.mem B (slot w aX) w ∧
      wv s.mem B (slot w aX) w < wv s.mem B (slot w aN) w)) ∧ t.mem = f.mem) ?_ rfl)
    fun t ⟨⟨ht, htm⟩, hkt⟩ =>
      ⟨ht, htm.trans (hfm.trans (hzm.trans (hvm.trans hum))),
        ((((hku.trans hkv).trans hkz).trans hkf).trans hkt).mono (by decide)⟩
  have he : (!decide (f.gpr .r15 = 0) &&
      decide (wv s.mem B (slot w aX) w < wv s.mem B (slot w aN) w)) =
      decide ((if aboveOne then 1 else 0) < wv s.mem B (slot w aX) w ∧
        wv s.mem B (slot w aX) w < wv s.mem B (slot w aN) w) := by
    rw [decide_eq_decide.mpr hf15, ← decide_not, ← Bool.decide_and]
    exact decide_eq_decide.mpr (by omega)
  xrun [show BitVec.signExtend 64 (1 : BitVec 32) = 1 from rfl, mask_sbb, mask_lt_one,
    show BitVec.signExtend 64 (-1 : BitVec 32) = BitVec.allOnes 64 from rfl,
    mask_complement, hfbp, mask_intersect, he]
  change (mask (decide ((f.gpr .r15).toNat < 1)) ^^^ BitVec.allOnes 64) &&&
    mask (decide (wv s.mem B (slot w aX) w < wv s.mem B (slot w aN) w)) = _
  rw [mask_lt_one, mask_complement, mask_intersect, he]

end VG.Proof.Dsa.X86_64
