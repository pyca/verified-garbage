module
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words

import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Impl.Mont.X86.Sparse
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.TCB.X86.Isa
import VerifiedGarbage.TCB.X86.State

/-! # Carry and borrow chains for sparse x86 reduction -/

@[expose] public section

namespace VG.Proof.Mont.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Proof.Mont

theorem sparseChain_succ (acc : Nat) (op op' : AluOp) (k : Nat) :
    sparseChain acc op op' (k + 1) = sparseChain acc op op' k ++
      sparseStep acc k (if k = 0 then op else op') (k == 0) := by
  simp only [sparseChain, List.range_succ, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]

def multiWeight (useQ : Nat → Bool) : Nat → Nat
  | 0 => 0
  | k + 1 => multiWeight useQ k + if useQ k then 2 ^ (32 * k) else 0

theorem multiChain_succ (acc : Nat) (useQ : Nat → Bool) (k : Nat) :
    multiChain acc useQ (k + 1) = multiChain acc useQ k ++
      sparseStep acc k (if k = 0 then .add else .adc) (useQ k) := by
  simp only [multiChain, List.range_succ, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]

end VG.Proof.Mont.X86
