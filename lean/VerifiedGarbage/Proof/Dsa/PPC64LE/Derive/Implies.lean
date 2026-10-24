module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Derive.Front
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# `vg_dsa_derive_key` on PPC64LE: the contract on the registers and the stack

`deriveKey_implies`: `dContract` implies the shared contract.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Impl.Dsa.PPC64LE

theorem stackArgs_one (s : State) : List.map (stackArg s) (List.range 1) = [stackArg s 0] := rfl

theorem pairFacts_two (a b : Region) : Sig.conj (Sig.pairFacts [(a, true), (b, false)]) ↔ a.Disjoint b := by
  simp [Sig.pairFacts, Sig.conj, List.filterMap_cons, List.filterMap_nil]

/-- A state meeting `dContract.pre`: 1024-bit p and 160-bit q, `out` at
`0x4000`, the domain at `0x1000`, x at `0x2000` and the working space at
`0x10000`; its size on the stack at `0x9060`. -/
def deriveSatState : State where
  gpr r := match r with
    | .r3 => 0x4000 | .r4 => 424 | .r5 => 0x1000 | .r6 => 276 | .r7 => 128 | .r8 => 0x2000 | .r9 => 20
    | .r10 => 0x10000 | _ => 0
  lr := 0
  sp := 0x9000
  mem a := bif Nat.beq a.toNat 0x9061 then 0x08 else 0
  rd := [⟨0x1000, 276⟩, ⟨0x2000, 20⟩, ⟨0x9060, 8⟩]
  wr := [⟨0x4000, 424⟩, ⟨0x10000, 16384⟩]

theorem deriveKey_implies : dContract.Implies (Spec.Dsa.deriveKeyContract abi) := by
  sig_implies [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, dContract, dRes, stackArgs_one,
    List.append_eq, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts, List.filterMap_cons,
    List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false, List.cons_append,
    List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append, pairFacts_two]
    [deriveSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using deriveSatState

end VG.Proof.Dsa.PPC64LE
