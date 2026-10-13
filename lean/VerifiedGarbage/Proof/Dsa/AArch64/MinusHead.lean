module

public import VerifiedGarbage.Proof.Dsa.AArch64.MinusStep
public import VerifiedGarbage.Proof.Dsa.AArch64.Masks
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-! # The first limb of DSA modulus-minus constants -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

abbrev minusHead (amount : Nat) : List Instr :=
  [ldh .x12 sW, ldh .x16 (sArr aN), ldh .x17 (sArr aY), movi .x7 0, movi .x4 amount,
    ld .x3 .x16, .subs .x .x3 .x3 .x4, st .x3 .x17, next .x16, next .x17, .subImm .x .x14 .x12 1]

theorem minusHead_ok {s : State} {B : Addr} {Z w amount : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w) (ha : amount < 2 ^ 16) :
    WP isa (.block (minusHead amount)) s fun t =>
      t.gpr .x12 = BitVec.ofNat 64 w ∧ t.gpr .x16 = off B (slot w aN + 8) ∧
      t.gpr .x17 = off B (slot w aY + 8) ∧ t.gpr .x14 = BitVec.ofNat 64 (w - 1) ∧ t.gpr .x7 = 0 ∧
      Outside B (slot w aY) 8 s.mem t.mem ∧
      wv t.mem B (slot w aY) 1 + amount = wv s.mem B (slot w aN) 1 + 2 ^ 64 * (!t.c).toNat ∧
      Keep [.x3, .x4, .x7, .x12, .x14, .x16, .x17] s t := by
  have hn := Nat.le_trans (slot_le (w := w) (show aN < 8 by decide)) hZ
  have hy := Nat.le_trans (slot_le (w := w) (show aY < 8 by decide)) hZ
  have hbound := hg.scr.nowrap
  refine WP.mono (WP.keep [.x3, .x4, .x7, .x12, .x14, .x16, .x17] (Q := fun t =>
    t.gpr .x12 = BitVec.ofNat 64 w ∧ t.gpr .x16 = off B (slot w aN + 8) ∧
    t.gpr .x17 = off B (slot w aY + 8) ∧ t.gpr .x14 = BitVec.ofNat 64 (w - 1) ∧ t.gpr .x7 = 0 ∧
    t.gpr .x4 = BitVec.setWidth 64 (BitVec.ofNat 16 amount) ∧
    t.mem = s.mem.writeW (off B (slot w aY))
      (word s.mem B (slot w aN) + ~~~(t.gpr .x4) + BitVec.ofNat 64 (true).toNat) ∧
    t.c = decide (2 ^ 64 ≤ (word s.mem B (slot w aN)).toNat + (~~~(t.gpr .x4)).toNat + (true).toNat))
    ?_ rfl rfl rfl) fun t ⟨⟨h12, h16, h17, h14, h7, h4, hm, hc⟩, hk⟩ => ?_
  · unfold minusHead
    brun [hg.x0, hdr_enc (show sW < 32 by decide), hdr_enc (sArr_lt (show aN < 8 by decide)),
      hdr_enc (sArr_lt (show aY < 8 by decide)), hg.ld hZ (show sW < 32 by decide),
      hg.ld hZ (sArr_lt (show aN < 8 by decide)), hg.ld hZ (sArr_lt (show aY < 8 by decide)), hg.hdr.hw,
      hg.hdr.harr aN (by decide), hg.hdr.harr aY (by decide), hg.scr.ld (show slot w aN + 8 ≤ Z by omega),
      hg.scr.st (show slot w aY + 8 ≤ Z by omega), ofNat_sub_one hw]
  · have hs := sbcs_toNat' (word s.mem B (slot w aN)) (t.gpr .x4) true
    have h4n : (t.gpr .x4).toNat = amount := by
      rw [h4, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (by omega)]
    rw [← hc, h4n] at hs
    generalize (word s.mem B (slot w aN) + ~~~(t.gpr .x4) + BitVec.ofNat 64 (true).toNat) = r at hs hm
    refine ⟨h12, h16, h17, h14, h7, by rw [hm]; exact writeW_outside _ _ _ (by omega), ?_, hk⟩
    rw [hm]
    simp only [wv, Nat.mul_zero, Nat.add_zero, Nat.zero_add, Nat.pow_zero, Nat.one_mul, word_writeW_self]
    simpa only [Bool.not_true, Bool.toNat_false, Nat.add_zero] using hs

end VG.Proof.Dsa.AArch64
