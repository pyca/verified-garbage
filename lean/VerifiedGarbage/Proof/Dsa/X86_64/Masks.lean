module

import VerifiedGarbage.Proof.Dsa.X86_64.Operands
public import VerifiedGarbage.Impl.Dsa.X86_64.Checks
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Dsa.Layout
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual

/-! # DSA rejection-mask arithmetic and accumulation -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

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

/-- Intersect an existing acceptance mask with the new predicate. -/
theorem accumulate_ok {s : State} {B : Addr} {Z : Nat} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hZ : pWorkspace ≤ Z) {a b : Bool}
    (ha : s.gpr .rax = mask a) (hb : word s.mem B Field.mask.offset = mask b) :
    WP isa (.block Checks.accumulate) s fun t =>
      word t.mem B Field.mask.offset = mask (a && b) ∧
      Outside B Field.mask.offset 8 s.mem t.mem ∧ Keep [.rax] s t := by
  have he : Field.mask.offset + 8 ≤ Z := Nat.le_trans (VG.Proof.Dsa.field_bounds .mask).2 hZ
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
    t.mem = s.mem.writeW (off B Field.mask.offset) (mask (a && b))) ?_ rfl)
    fun t ⟨hm, hk⟩ => ?_
  · unfold Checks.accumulate Core.field
    xrun [State.ea, hdi, fieldAddress, hs.ld he, hs.st he, ha, hb, mask_intersect]
  · exact ⟨by rw [hm, word_writeW_self], by rw [hm]; exact writeW_outside _ _ _ (by have := hs.nowrap; omega), hk⟩

end VG.Proof.Dsa.X86_64
