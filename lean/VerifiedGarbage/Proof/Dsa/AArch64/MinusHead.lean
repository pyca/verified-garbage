module
public import Mathlib.Data.Int.GCD
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public import VerifiedGarbage.Proof.Framework.Contract

import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
import VerifiedGarbage.Proof.Bignum.AArch64.Csub
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! # First limb and public counter for modulus-minus constants -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

abbrev minusHead (amount : Nat) : List Instr :=
  [ldh .x14 sW, ldh .x16 (sArr aN), ldh .x17 (sArr aY), movi .x4 amount,
    movi .x7 0, ld .x3 .x16, .subs .x .x3 .x3 .x4, st .x3 .x17,
    next .x16, next .x17, .subImm .x .x14 .x14 1]

theorem minusHead_ok {s : State} {B : Addr} {Z w amount : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 31)
    (ha : amount < 2 ^ 16) :
    WP isa (.block (minusHead amount)) s fun t =>
      t.gpr .x14 = BitVec.ofNat 64 (w - 1) ∧ t.gpr .x16 = off B (slot w aN + 8) ∧
      t.gpr .x17 = off B (slot w aY + 8) ∧ t.gpr .x7 = 0 ∧ Outside B (slot w aY) 8 s.mem t.mem ∧
      wv t.mem B (slot w aY) 1 + amount = wv s.mem B (slot w aN) 1 + 2 ^ 64 * (!t.c).toNat ∧
      Keep mmRegs s t := by
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 :=
    fun i hi => hg.ld hZ hi
  have hn := Nat.le_trans (slot_le (w := w) (show aN < 8 by decide)) hZ
  have hy := Nat.le_trans (slot_le (w := w) (show aY < 8 by decide)) hZ
  have hz := hg.scr.nowrap
  have ham : (BitVec.ofNat 16 amount).setWidth 64 = BitVec.ofNat 64 amount := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  have hsub : BitVec.ofNat 64 w - (1#64) = BitVec.ofNat 64 (w - 1) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    simp only [Nat.mod_eq_of_lt (show 1 < 2 ^ 64 by decide)]
    omega
  refine WP.mono (WP.keep [.x14, .x16, .x17, .x4, .x7, .x3] (Q := fun t =>
    t.gpr .x14 = BitVec.ofNat 64 (w - 1) ∧ t.gpr .x16 = off B (slot w aN + 8) ∧
    t.gpr .x17 = off B (slot w aY + 8) ∧ t.gpr .x7 = 0 ∧ ∃ r : BitVec 64,
    t.mem = s.mem.writeW (off B (slot w aY)) r ∧
    r.toNat + amount = (word s.mem B (slot w aN)).toNat + 2 ^ 64 * (!t.c).toNat) ?_ rfl rfl rfl)
    fun t ⟨⟨ht14, ht16, ht17, ht7, r, htm, hv⟩, hk⟩ => ?_
  · unfold minusHead
    brun [hg.x0, hdr_enc (show sW < 32 by decide), hdr_enc (show sArr aN < 32 by decide), hdr_enc (show sArr aY < 32 by decide),
      hl sW (by decide), hl (sArr aN) (by decide), hl (sArr aY) (by decide),
      hg.hdr.hw, hg.hdr.harr aN (by decide), hg.hdr.harr aY (by decide), ham, hsub,
      hg.scr.ld (show slot w aN + 8 ≤ Z by omega), hg.scr.st (show slot w aY + 8 ≤ Z by omega)]
    refine ⟨_, rfl, ?_⟩
    simpa only [Bool.toNat_true, Bool.not_true, Bool.toNat_false, Nat.add_zero,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show amount < 2 ^ 64 by omega)] using
      sbcs_toNat (word s.mem B (slot w aN)) (BitVec.ofNat 64 amount) true
  · refine ⟨ht14, ht16, ht17, ht7, ?_, ?_, hk.mono (by decide)⟩
    · rw [htm]; exact writeW_outside _ _ _ (by omega)
    · rw [htm]
      simpa only [wv, Nat.mul_zero, Nat.add_zero, Nat.zero_add, Nat.pow_zero, Nat.one_mul,
        word_writeW_self] using hv

end VG.Proof.Dsa.AArch64
