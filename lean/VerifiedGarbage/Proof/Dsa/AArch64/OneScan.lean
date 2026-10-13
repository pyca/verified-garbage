module

public import VerifiedGarbage.Proof.Dsa.Words
public import VerifiedGarbage.Proof.Dsa.AArch64.OrWords
public import VerifiedGarbage.Proof.Dsa.AArch64.ZeroMask
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-! # DSA subgroup checks against the ordinary value one -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

abbrev oneScanHead : List Instr := [ldh .x12 sW, ldh .x16 (sArr aX), ld .x9 .x16, movi .x4 1,
  .logic .eor .x .x9 .x9 .x4, next .x16, .subImm .x .x14 .x12 1]

abbrev oneScanLoop : Prog isa := countLoop .x14 [ld .x3 .x16, .logic .orr .x .x9 .x9 .x3, next .x16]

theorem oneScanHead_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w) :
    WP isa (.block oneScanHead) s fun t =>
      t.gpr .x12 = BitVec.ofNat 64 w ∧ t.gpr .x16 = off B (slot w aX + 8) ∧
      t.gpr .x14 = BitVec.ofNat 64 (w - 1) ∧
      t.gpr .x9 = word s.mem B (slot w aX) ^^^ 1 ∧ t.mem = s.mem ∧
      Keep [.x4, .x9, .x12, .x14, .x16] s t := by
  have hx := Nat.le_trans (slot_le (w := w) (show aX < 8 by decide)) hZ
  refine WP.mono (WP.keep [.x4, .x9, .x12, .x14, .x16] (Q := fun t =>
    t.gpr .x12 = BitVec.ofNat 64 w ∧ t.gpr .x16 = off B (slot w aX + 8) ∧
    t.gpr .x14 = BitVec.ofNat 64 (w - 1) ∧
    t.gpr .x9 = word s.mem B (slot w aX) ^^^ 1 ∧ t.mem = s.mem) ?_ (by decide) (by decide) (by decide +kernel))
    fun t ⟨h, hk⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2, hk⟩
  unfold oneScanHead
  brun [hg.x0, hdr_enc (show sW < 32 by decide), hdr_enc (sArr_lt (show aX < 8 by decide)),
    hg.ld hZ (show sW < 32 by decide), hg.ld hZ (sArr_lt (show aX < 8 by decide)), hg.hdr.hw,
    hg.hdr.harr aX (by decide), hg.scr.ld (show slot w aX + 8 ≤ Z by omega), ofNat_sub_one hw]
  rfl

/-- Fixed-count comparison with one, retaining the boolean in the accumulator. -/
theorem oneScan_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31) :
    WP isa (.seq (.block oneScanHead) oneScanLoop) s fun t =>
      (t.gpr .x9 = 0 ↔ wv s.mem B (slot w aX) w = 1) ∧ t.mem = s.mem ∧
      Keep [.x3, .x4, .x9, .x12, .x14, .x16, .x17] s t := by
  have hx := Nat.le_trans (slot_le (w := w) (show aX < 8 by decide)) hZ
  refine WP.seq (WP.mono (oneScanHead_ok hg hZ (by omega)) fun u ⟨_, hu16, hu14, hu9, hum, hku⟩ => ?_)
  have hlow : u.gpr .x9 = 0 ↔ (word u.mem B (slot w aX) ^^^ 1) = 0 := by rw [hu9, hum]
  refine WP.mono (orWords_ok (hg.scr.congr hku.wr) hu16 hu14 hlow hw hw' (by omega))
    fun t ⟨ht, htm, hkt⟩ => ?_
  rw [VG.Proof.Dsa.words_eq_one (by omega), hum] at ht
  exact ⟨ht, htm.trans hum, (hku.trans hkt).mono (by decide)⟩

end VG.Proof.Dsa.AArch64
