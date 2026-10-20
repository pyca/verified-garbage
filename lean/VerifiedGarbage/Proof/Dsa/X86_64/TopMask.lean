module
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp

import VerifiedGarbage.Proof.Dsa.X86_64.Masks
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Dsa.X86_64.Operands

/-! # Testing byte-aligned modulus bit lengths -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem byte_top_mask (b : Byte) :
    (0#64 - (BitVec.ofBool (decide ((b.zeroExtend 64).toNat < 128))).setWidth 64) ^^^ BitVec.allOnes 64 =
      mask (decide (128 ≤ b.toNat)) := by
  change mask (decide ((b.setWidth 64).toNat < 128)) ^^^ BitVec.allOnes 64 = _
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans b.isLt (show 2 ^ 8 < 2 ^ 64 by decide)),
    mask_complement, ← decide_not]
  exact congrArg mask (decide_eq_decide.mpr (by omega))

/-- The first significant byte must have its high bit set for an exact
byte-aligned DSA bit length. -/
theorem topMask_ok {s : State} {b : Byte} (h9 : s.gpr .r9 = b.zeroExtend 64) :
    WP isa (.block [.alu .cmp .r9 (.imm 128), .alu .sbb .rax (.reg .rax), .alu .xor .rax (.imm (-1))]) s fun t =>
      t.gpr .rax = mask (decide (128 ≤ b.toNat)) ∧ t.mem = s.mem ∧ Keep [.rax, .r9] s t := by
  refine WP.mono (WP.keep [.rax, .r9] (Q := fun t =>
    t.gpr .rax = mask (decide (128 ≤ b.toNat)) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨⟨ht, hm⟩, hk⟩ => ⟨ht, hm, hk⟩
  xrun [h9, show BitVec.signExtend 64 (128 : BitVec 32) = 128#64 from rfl,
    show BitVec.signExtend 64 (-1 : BitVec 32) = BitVec.allOnes 64 from rfl]
  exact byte_top_mask b

end VG.Proof.Dsa.X86_64
