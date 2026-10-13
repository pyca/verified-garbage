module

public import VerifiedGarbage.Proof.Dsa.AArch64.Operands
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
public import VerifiedGarbage.Impl.Dsa.AArch64.Checks
public import VerifiedGarbage.Impl.Dsa.AArch64.Checks
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-! # DSA rejection-mask arithmetic and accumulation -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem mask_sbb (x : BitVec 64) (c : Bool) : x - x - (BitVec.ofBool c).setWidth 64 = mask c := by
  cases c <;> simp [mask]

theorem mask_complement (b : Bool) : mask b ^^^ BitVec.allOnes 64 = mask (!b) := by
  cases b <;> decide

theorem mask_intersect (a b : Bool) : mask a &&& mask b = mask (a && b) := by
  cases a <;> cases b <;> decide

theorem mask_lt_one (x : BitVec 64) : decide (x.toNat < 1) = decide (x = 0) := by
  apply decide_eq_decide.mpr
  rw [Nat.lt_one_iff]
  exact ⟨fun h => BitVec.eq_of_toNat_eq h, fun h => congrArg BitVec.toNat h⟩

/-- The carry of `x - n` (`subs` with a 16-bit `movz` operand): `n ≤ x`. -/
theorem subs_carry (x : BitVec 64) {n : Nat} (hn : n < 2 ^ 16) :
    decide (2 ^ 64 ≤ x.toNat + (~~~(BitVec.setWidth 64 (BitVec.ofNat 16 n))).toNat + (true).toNat) =
      decide (n ≤ x.toNat) := by
  have h1 : (~~~(BitVec.setWidth 64 (BitVec.ofNat 16 n))).toNat = 2 ^ 64 - 1 - n := by
    rw [BitVec.toNat_not, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show n < 2 ^ 16 by omega), Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega)]
  rw [h1, Bool.toNat_true]
  have := x.isLt
  apply decide_eq_decide.mpr
  omega

theorem csel_carry_mask (c : Bool) :
    (if c then BitVec.setWidth 64 (0#16) - 1#64 else BitVec.setWidth 64 (0#16)) = mask c := by
  cases c <;> rfl

/-- `x15 :=` all ones iff `x3` is zero; `x4 :=` all ones, `x7 := 0`. -/
theorem zeroMask_ok (s : State) :
    WP isa (.block Checks.zeroMask) s fun t =>
      (t.gpr .x15 = mask (decide (s.gpr .x3 = 0)) ∧ t.gpr .x4 = mask true ∧ t.gpr .x7 = 0 ∧
        t.mem = s.mem) ∧ Keep [.x3, .x4, .x7, .x15] s t := by
  refine WP.keep [.x3, .x4, .x7, .x15] ?_ (by decide) (by decide) (by decide +kernel)
  unfold Checks.zeroMask Impl.Rsa.AArch64.Crt.borrowMask
  brun [subs_one_c, csel_mask']
  cases decide (s.gpr .x3 = 0) <;> rfl

/-- `x15 :=` all ones iff `x3 ≥ n`; `x4 :=` all ones, `x7 := 0`. -/
theorem atLeast_ok (s : State) {n : Nat} (hn : n < 2 ^ 16) :
    WP isa (.block (Checks.atLeast n)) s fun t =>
      (t.gpr .x15 = mask (decide (n ≤ (s.gpr .x3).toNat)) ∧ t.mem = s.mem) ∧
        Keep [.x3, .x4, .x7, .x15] s t := by
  refine WP.keep [.x3, .x4, .x7, .x15] ?_ rfl rfl rfl
  unfold Checks.atLeast Checks.carryMask
  brun [subs_carry _ hn, csel_carry_mask]

/-- Intersect an existing acceptance mask with the new predicate in `x15`. -/
theorem accumulate_ok {s : State} {B : Addr} {Z : Nat} (hs : Scr s B Z)
    (hdi : s.gpr .x0 = B) (hZ : pWorkspace ≤ Z) {a b : Bool}
    (ha : s.gpr .x15 = mask a) (hb : word s.mem B Field.mask.offset = mask b) :
    WP isa (.block Checks.accumulate) s fun t =>
      word t.mem B Field.mask.offset = mask (a && b) ∧
      Outside B Field.mask.offset 8 s.mem t.mem ∧ Keep [.x3, .x15] s t := by
  have he : Field.mask.offset + 8 ≤ Z := Nat.le_trans (VG.Proof.Dsa.field_bounds .mask).2 hZ
  refine WP.mono (WP.keep [.x3, .x15] (Q := fun t =>
    t.mem = s.mem.writeW (off B Field.mask.offset) (mask (a && b))) ?_ (by decide) (by decide)
      (by decide +kernel))
    fun t ⟨hm, hk⟩ => ?_
  · unfold Checks.accumulate Core.field
    brun [hdi, field_enc, hs.ld he, hs.st he, ha, hb]
    rw [BitVec.and_comm, mask_intersect, Bool.and_comm]
  · exact ⟨by rw [hm, word_writeW_self], by rw [hm]; exact writeW_outside _ _ _ (by have := hs.nowrap; omega), hk⟩

end VG.Proof.Dsa.AArch64
