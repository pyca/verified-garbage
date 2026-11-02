module

public import VerifiedGarbage.Proof.Dsa.RISCV64.DeriveFront
public import VerifiedGarbage.Proof.Dsa.RISCV64.VerifyImplies
import VerifiedGarbage.Proof.Dsa.RISCV64.DeriveFn
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# `vg_dsa_derive_key` on RISC-V: the contract on the registers and the stack

`deriveKey_implies`: `dContract` implies the shared contract; `deriveKey_wp`:
`vg_dsa_derive_key` meets the shared contract's precondition and
postcondition, and the calling convention, with no stack of its own.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.Impl.Dsa.RISCV64

theorem stackArgs_one (s : State) : List.map (stackArg s) (List.range 1) = [stackArg s 0] := rfl

/-- A state meeting `dContract.pre`: 1024-bit p and 160-bit q, `out` at
`0x4000`, the domain at `0x1000`, x at `0x2000` and the working space at
`0x10000`; its size on the stack at `0x9000`. -/
def deriveSatState : State where
  gpr r := match r with
    | .a0 => 0x4000 | .a1 => 424 | .a2 => 0x1000 | .a3 => 276 | .a4 => 128 | .a5 => 0x2000 | .a6 => 20
    | .a7 => 0x10000 | _ => 0
  sp := 0x9000
  mem a := bif Nat.beq a.toNat 0x9001 then 0x08 else 0
  rd := [⟨0x1000, 276⟩, ⟨0x2000, 20⟩, ⟨0x9000, 8⟩]
  wr := [⟨0x4000, 424⟩, ⟨0x10000, 16384⟩]

theorem deriveKey_implies : dContract.Implies (Spec.Dsa.deriveKeyContract RISCV64.abi) := by
  sig_implies [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, RISCV64.abi, RISCV64.argRegs, dContract, dRes,
    stackArgs_one, List.append_eq, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts, List.filterMap_cons,
    List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false, List.cons_append,
    List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append, pairFacts_two, List.range, List.range.loop]
    [deriveSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using deriveSatState

/-- `vg_dsa_derive_key` under the shared contract. -/
theorem deriveKey_wp (s : State) (h : (Spec.Dsa.deriveKeyContract RISCV64.abi).pre s) :
    WP isa Derive.derive s fun t => abiPreserved s t ∧ (Spec.Dsa.deriveKeyContract RISCV64.abi).post s t := by
  obtain ⟨tr, t, he, ha, hp⟩ := deriveKey_correct s (deriveKey_implies.pre s h)
  exact ⟨tr, t, he, ha, deriveKey_implies.post s t h hp⟩

end VG.Proof.Dsa.RISCV64
