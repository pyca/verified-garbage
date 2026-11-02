module

public import VerifiedGarbage.Proof.Dsa.RISCV64.VerifyFront
import VerifiedGarbage.Proof.Dsa.RISCV64.VerifyFn
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# `vg_dsa_verify` on RISC-V: the contract on the registers and the stack

`verify_implies`: `vContract` implies the shared contract; `verify_wp`:
`vg_dsa_verify` meets the shared contract's precondition and postcondition,
and the calling convention, with no stack of its own.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.Impl.Dsa.RISCV64

theorem stackArgs_two (s : State) : List.map (stackArg s) (List.range 2) = [stackArg s 0, stackArg s 1] := rfl

theorem pairFacts_two (a b : Region) : Sig.conj (Sig.pairFacts [(a, true), (b, false)]) ↔ a.Disjoint b := by
  simp [Sig.pairFacts, Sig.conj]

/-- A state meeting `vContract.pre`: 1024-bit p and 160-bit q, the key at
`0x1000`, the signature at `0x2000`, the digest at `0x3000` and the working
space at `0x10000`, its address and size on the stack at `0x9000`. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 404 | .a2 => 128 | .a3 => 20 | .a4 => 0x2000 | .a5 => 40 | .a6 => 0x3000
    | .a7 => 20 | _ => 0
  sp := 0x9000
  mem a := bif Nat.beq a.toNat 0x9002 then 0x01 else bif Nat.beq a.toNat 0x9009 then 0x08 else 0
  rd := [⟨0x1000, 404⟩, ⟨0x2000, 40⟩, ⟨0x3000, 20⟩, ⟨0x9000, 16⟩]
  wr := [⟨0x10000, 16384⟩]

theorem verify_implies : vContract.Implies (Spec.Dsa.verifyContract RISCV64.abi) := by
  sig_implies [Spec.Dsa.verifyContract, Spec.Dsa.verifySig, RISCV64.abi, RISCV64.argRegs, vContract,
    stackArgs_two, List.append_eq, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts, List.filterMap_cons,
    List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false, List.cons_append,
    List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append, pairFacts_two, List.range, List.range.loop]
    [satState, stackArg, stackArgAddr, Mem.readW, Mem.read] using satState

/-- `vg_dsa_verify` under the shared contract. -/
theorem verify_wp (s : State) (h : (Spec.Dsa.verifyContract RISCV64.abi).pre s) :
    WP isa Verify.verify s fun t => abiPreserved s t ∧ (Spec.Dsa.verifyContract RISCV64.abi).post s t := by
  obtain ⟨tr, t, he, ha, hp⟩ := verify_correct s (verify_implies.pre s h)
  exact ⟨tr, t, he, ha, verify_implies.post s t h hp⟩

end VG.Proof.Dsa.RISCV64
