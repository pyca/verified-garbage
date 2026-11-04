module

public import VerifiedGarbage.Spec.RsaPss.Precomputed
public import VerifiedGarbage.Proof.RsaPss.AArch64.SignPre
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.PrecomputedCorrect
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract

/-!
# RSASSA-PSS verification on AArch64: the precondition

The buffers of `verifyPrecomputedTableContract` on AArch64, and the
proof that its precondition is unsatisfiable under the current model of
AArch64's stack arguments (`pre_unsat`): its verification waits for that
model to accept the layout.
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Vfy

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.RsaPkcs1Sig.AArch64.Pc (stackArgs_five)
open VG.Proof.RsaPss.AArch64.Sgn (stk kR fb kb frame_sub0 stackArgAddr_eq keep_of_frame)

/-- The buffers: `n`, `e`, the digest, the signature, the working space, the
precomputed values, the tables and the arguments on the stack. -/
abbrev nR (s : State) : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
abbrev eR (s : State) : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
abbrev dgR (s : State) : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat⟩
abbrev sgR (s : State) : Region := ⟨s.gpr .x6, (s.gpr .x7).toNat⟩
abbrev sR (s : State) : Region := ⟨stackArg s 2, (stackArg s 3).toNat * 8⟩
abbrev pR (s : State) : Region := ⟨stackArg s 4, (stackArg s 5).toNat * 8⟩
abbrev tHR (s : State) : Region := Sig.tableRegion 64 (stackArg s 6) 11
abbrev tGR (s : State) : Region := Sig.tableRegion 64 (stackArg s 7) 5
abbrev aR (s : State) : Region := ⟨stackArgAddr s 0, 64⟩

/-- The ABI the contract states, with the tables. -/
abbrev verifyAbi (tsH tsG : List FnTable) : Abi isa :=
  abi.withTables Spec.RsaPss.verifyPrecomputedTableSig [("hash", tsH), ("mgf1", tsG)]

/-- The contract's precondition is unsatisfiable on AArch64 as `TCB/AArch64/Target.lean`
models its stack arguments: with `digest` a slice, `salt_len` (64 bits) is the first
stack argument and `any_salt_len` (32 bits) the second, a layout `abi.args` does not
accept (only a first 32-bit stack argument is: `firstNarrowStack`). Proving the
verification needs that layout in the model first. -/
theorem pre_unsat {tsH tsG : List FnTable} {K : Nat} {s : State} :
    ¬ (Spec.RsaPss.verifyPrecomputedTableContract (verifyAbi tsH tsG) (stk K)).pre s := by
  intro h
  sig_iff at h
  sig_reduce [Spec.RsaPss.verifyPrecomputedTableContract, Spec.RsaPss.verifyPrecomputedTableSig,
    Spec.MdHashTable.param, Spec.HashTable.param,
    Spec.MdHashTable.wordCount, Spec.HashTable.wordCount, Spec.MdHashTable.fns, Spec.HashTable.fns,
    Spec.MdHashTable.dataWords, Spec.HashTable.dataWords, Abi.withTables, Sig.wordIndex, abi, argRegs,
    List.append_eq, _root_.List.range, _root_.List.range.loop] at h
  exact h

end VG.Proof.RsaPss.AArch64.Vfy
