module
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp

import VerifiedGarbage.Proof.Dsa.X86_64.Masks
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Turning a zero or equality accumulator into an acceptance mask -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- Compare an accumulator with zero without branching, optionally invert
the predicate. Used for both zero tests and byte-string equality. -/
theorem zeroMask_ok (r : Reg) (invert : Bool) {s : State} :
    WP isa (.block (([.alu .cmp r (.imm 1), .alu .sbb .rax (.reg .rax)] : List Instr) ++
      (if invert then [.alu .xor .rax (.imm (-1))] else []))) s fun t =>
      t.gpr .rax = mask (if invert then !decide (s.gpr r = 0) else decide (s.gpr r = 0)) ∧
      t.mem = s.mem ∧ Keep [.rax, r] s t := by
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, r] (Q := fun u =>
    u.gpr .rax = mask (decide (s.gpr r = 0)) ∧ u.mem = s.mem) ?_ ?_)
    fun u ⟨⟨hua, hum⟩, hku⟩ => ?_
  · xrun [show BitVec.signExtend 64 (1 : BitVec 32) = 1 from rfl]
    change mask (decide ((s.gpr r).toNat < 1)) = _
    rw [mask_lt_one]
  · cases r <;> rfl
  · refine WP.mono (WP.keep [.rax] (Q := fun t =>
      t.gpr .rax = mask (if invert then !decide (s.gpr r = 0) else decide (s.gpr r = 0)) ∧
      t.mem = u.mem) ?_ ?_) fun t ⟨⟨hta, htm⟩, hkt⟩ =>
        ⟨hta, htm.trans hum, (hku.trans hkt).mono (by simp)⟩
    · cases invert <;> simp only [Bool.false_eq_true, ite_false, ite_true]
      · exact WP.block_nil ⟨hua, rfl⟩
      · xrun [hua, show BitVec.signExtend 64 (-1 : BitVec 32) = BitVec.allOnes 64 from rfl, mask_complement]
    · cases invert <;> rfl

end VG.Proof.Dsa.X86_64
