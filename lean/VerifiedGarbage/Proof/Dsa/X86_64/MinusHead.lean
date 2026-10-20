module
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont

import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual

/-! # The first limb of DSA modulus-minus constants -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

abbrev minusHead (amount : Nat) : List Instr :=
  [.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr aN))),
    .mov .rbx (.mem (hdr (sArr aY))), .mov .rax (.mem (at0 .rsi)),
    .alu .sub .rax (.imm (BitVec.ofNat 32 amount)), .store (at0 .rbx) .rax, cfToRbp]

theorem minusHead_ok {s : State} {B : Addr} {Z w amount : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (ha : amount < 2 ^ 31) :
    WP isa (.block (minusHead amount)) s fun t =>
      t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .rsi = off B (slot w aN) ∧
      t.gpr .rbx = off B (slot w aY) ∧ Outside B (slot w aY) 8 s.mem t.mem ∧
      (∃ c : Bool, t.gpr .rbp = mask c ∧
        wv t.mem B (slot w aY) 1 + amount = wv s.mem B (slot w aN) 1 + 2 ^ 64 * c.toNat) ∧
      Keep [.r12, .rsi, .rbx, .rax, .rbp] s t := by
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (Nat.le_trans (hdr_lt_slot w 8 hi) hZ)
  have hn := Nat.le_trans (slot_le (w := w) (show aN < 8 by decide)) hZ
  have hy := Nat.le_trans (slot_le (w := w) (show aY < 8 by decide)) hZ
  have hbound := hg.scr.nowrap
  refine WP.mono (WP.keep [.r12, .rsi, .rbx, .rax, .rbp] (Q := fun t =>
    t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .rsi = off B (slot w aN) ∧
    t.gpr .rbx = off B (slot w aY) ∧ ∃ c : Bool, t.gpr .rbp = mask c ∧
    ∃ r : BitVec 64, t.mem = s.mem.writeW (off B (slot w aY)) r ∧
      r.toNat + amount = (word s.mem B (slot w aN)).toNat + 2 ^ 64 * c.toNat) ?_ rfl)
    fun t ⟨⟨ht12, htsi, htbx, c, htc, r, htm, hval⟩, hk⟩ => ?_
  · unfold minusHead cfToRbp
    xrun [State.ea, hdr, at0, hg.rdi, hdrOff, hl sW (by decide), hl (sArr aN) (by decide),
      hl (sArr aY) (by decide), hg.hdr.hw, hg.hdr.harr aN (by decide), hg.hdr.harr aY (by decide),
      hg.scr.ld (show slot w aN + 8 ≤ Z by omega), hg.scr.st (show slot w aY + 8 ≤ Z by omega),
      show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, sx_ofNat ha]
    refine ⟨_, rfl, _, rfl, ?_⟩
    have h := sbb_toNat (word s.mem B (slot w aN)) (BitVec.ofNat 64 amount) false
    simpa only [Bool.toNat_false, Nat.add_zero,
      show (BitVec.ofBool false).setWidth 64 = 0#64 from rfl, BitVec.sub_zero,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show amount < 2 ^ 64 by omega)] using h
  · refine ⟨ht12, htsi, htbx, ?_, ⟨c, htc, ?_⟩, hk⟩
    · rw [htm]; exact writeW_outside _ _ _ (by omega)
    · rw [htm]
      simpa only [wv, Nat.mul_zero, Nat.add_zero, Nat.zero_add, Nat.pow_zero, Nat.one_mul,
        word_writeW_self] using hval

end VG.Proof.Dsa.X86_64
