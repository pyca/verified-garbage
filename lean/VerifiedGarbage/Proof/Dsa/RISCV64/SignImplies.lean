module

public import VerifiedGarbage.Proof.Dsa.RISCV64.SignFront
public import VerifiedGarbage.Proof.Dsa.RISCV64.VerifyImplies
import VerifiedGarbage.Proof.Dsa.RISCV64.SignFn
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# `vg_dsa_sign` on RISC-V: the contract on the registers and the stack

`sign_implies`: `sContract` implies the shared contract; `sign_wp`:
`vg_dsa_sign` meets the shared contract's precondition and postcondition,
and the calling convention, with no stack of its own.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.Impl.Dsa.RISCV64

theorem stackArgs_three (s : State) :
    List.map (stackArg s) (List.range 3) = [stackArg s 0, stackArg s 1, stackArg s 2] := rfl

theorem pairFacts_three (a b c : Region) :
    Sig.conj (Sig.pairFacts [(a, false), (b, true), (c, false)]) ↔ a.Disjoint b ∧ b.Disjoint c := by
  simp [Sig.pairFacts, Sig.conj, List.filterMap_cons, List.filterMap_nil]

/-- A state meeting `sContract.pre`: 1024-bit p and 160-bit q, `out` at
`0x4000`, the key at `0x1000`, the nonce at `0x2000`, the digest at `0x3000`
and the working space at `0x10000`; `digest_len`, its address and size on the
stack at `0x9000`. -/
def signSatState : State where
  gpr r := match r with
    | .a0 => 0x4000 | .a1 => 40 | .a2 => 0x1000 | .a3 => 424 | .a4 => 128 | .a5 => 0x2000 | .a6 => 20
    | .a7 => 0x3000 | _ => 0
  sp := 0x9000
  mem a := bif Nat.beq a.toNat 0x9000 then 20 else bif Nat.beq a.toNat 0x900a then 0x01 else
    bif Nat.beq a.toNat 0x9011 then 0x08 else 0
  rd := [⟨0x1000, 424⟩, ⟨0x2000, 20⟩, ⟨0x3000, 20⟩, ⟨0x9000, 24⟩]
  wr := [⟨0x4000, 40⟩, ⟨0x10000, 16384⟩]

theorem sign_implies : sContract.Implies (Spec.Dsa.signContract RISCV64.abi) := by
  sig_implies [Spec.Dsa.signContract, Spec.Dsa.signSig, RISCV64.abi, RISCV64.argRegs, sContract, sRes,
    stackArgs_three, List.append_eq, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts, List.filterMap_cons,
    List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false, List.cons_append,
    List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append, pairFacts_three, List.range, List.range.loop]
    [signSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using signSatState

/-- `vg_dsa_sign` under the shared contract. -/
theorem sign_wp (s : State) (h : (Spec.Dsa.signContract RISCV64.abi).pre s) :
    WP isa Sign.sign s fun t => abiPreserved s t ∧ (Spec.Dsa.signContract RISCV64.abi).post s t := by
  obtain ⟨tr, t, he, ha, hp⟩ := sign_correct s (sign_implies.pre s h)
  exact ⟨tr, t, he, ha, sign_implies.post s t h hp⟩

end VG.Proof.Dsa.RISCV64
