module
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp

public import VerifiedGarbage.Proof.Dsa.X86_64.Masks
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Bignum.X86_64.CTR2
import VerifiedGarbage.Spec.Dsa.SignVerify
public import VerifiedGarbage.Proof.Bignum.CrtMath
public import VerifiedGarbage.Proof.Bignum.LazyMath
public import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtRedc
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
public import VerifiedGarbage.Proof.Bignum.X86_64.Csub
public import VerifiedGarbage.Proof.Bignum.X86_64.Exp
public import VerifiedGarbage.Proof.Bignum.X86_64.Loop
public import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
public import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
public import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
public import VerifiedGarbage.Proof.Bignum.X86_64.Row
public import VerifiedGarbage.Proof.Bignum.X86_64.Valid
public import VerifiedGarbage.Proof.Dsa.Arithmetic
public import VerifiedGarbage.Proof.Dsa.X86_64.Arithmetic
public import VerifiedGarbage.Proof.Dsa.X86_64.Load
public import VerifiedGarbage.Proof.Dsa.X86_64.Operands
public import VerifiedGarbage.Proof.Dsa.X86_64.Prepare
public import VerifiedGarbage.Proof.Framework.RegSetOrder
public import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Framework.X86_64.Masked
public import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Bignum.CrtMath
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Bignum.X86_64.CTExp
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.X86_64.CrtRedc
import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.Double
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Setup
import VerifiedGarbage.Proof.Bignum.X86_64.Store
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.X86_64.Arithmetic
import VerifiedGarbage.Proof.Dsa.X86_64.Load
import VerifiedGarbage.Proof.Dsa.X86_64.Operands
import VerifiedGarbage.Proof.Dsa.X86_64.Prepare
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RelCT

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
