module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyFront
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# `vg_dsa_verify` on PPC64LE: the contract on the registers and the stack

`verify_implies`: `vContract` implies the shared contract.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Impl.Dsa.PPC64LE

theorem stackArgs_two (s : State) : List.map (stackArg s) (List.range 2) = [stackArg s 0, stackArg s 1] := rfl

theorem pairFacts_two (a b : Region) : Sig.conj (Sig.pairFacts [(a, true), (b, false)]) ↔ a.Disjoint b := by
  simp [Sig.pairFacts, Sig.conj]

/-- A state meeting `vContract.pre`: 1024-bit p and 160-bit q, the key at
`0x1000`, the signature at `0x2000`, the digest at `0x3000` and the working
space at `0x10000`, its address and size on the stack at `0x9060`. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 404 | .r5 => 128 | .r6 => 20 | .r7 => 0x2000 | .r8 => 40 | .r9 => 0x3000
    | .r10 => 20 | _ => 0
  lr := 0
  sp := 0x9000
  mem a := bif Nat.beq a.toNat 0x9062 then 0x01 else bif Nat.beq a.toNat 0x9069 then 0x08 else 0
  rd := [⟨0x1000, 404⟩, ⟨0x2000, 40⟩, ⟨0x3000, 20⟩, ⟨0x9060, 16⟩]
  wr := [⟨0x10000, 16384⟩]

theorem verify_implies : vContract.Implies (Spec.Dsa.verifyContract abi) := by
  sig_implies [Spec.Dsa.verifyContract, Spec.Dsa.verifySig, abi, argRegs, vContract, stackArgs_two,
    List.append_eq, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts, List.filterMap_cons,
    List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false, List.cons_append,
    List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append, pairFacts_two]
    [satState, stackArg, stackArgAddr, Mem.readW, Mem.read] using satState

end VG.Proof.Dsa.PPC64LE
