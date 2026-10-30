module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.Front
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig

/-!
# `vg_dsa_sign` on PPC64LE: the contract on the registers and the stack

`sign_implies`: `sContract` implies the shared contract.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Impl.Dsa.PPC64LE

theorem stackArgs_three (s : State) :
    List.map (stackArg s) (List.range 3) = [stackArg s 0, stackArg s 1, stackArg s 2] := rfl

theorem pairFacts_three (a b c : Region) :
    Sig.conj (Sig.pairFacts [(a, false), (b, true), (c, false)]) ↔ a.Disjoint b ∧ b.Disjoint c := by
  simp [Sig.pairFacts, Sig.conj_single, Sig.conj_cons_cons, List.filterMap_cons, List.filterMap_nil]

/-- A state meeting `sContract.pre`: 1024-bit p and 160-bit q, `out` at
`0x4000`, the key at `0x1000`, the nonce at `0x2000`, the digest at `0x3000`
and the working space at `0x10000`; `digest_len`, its address and size on the
stack at `0x9060`. -/
def signSatState : State where
  gpr r := match r with
    | .r3 => 0x4000 | .r4 => 40 | .r5 => 0x1000 | .r6 => 424 | .r7 => 128 | .r8 => 0x2000 | .r9 => 20
    | .r10 => 0x3000 | _ => 0
  lr := 0
  sp := 0x9000
  mem a := bif Nat.beq a.toNat 0x9060 then 20 else bif Nat.beq a.toNat 0x906a then 0x01 else
    bif Nat.beq a.toNat 0x9071 then 0x08 else 0
  rd := [⟨0x1000, 424⟩, ⟨0x2000, 20⟩, ⟨0x3000, 20⟩, ⟨0x9060, 24⟩]
  wr := [⟨0x4000, 40⟩, ⟨0x10000, 16384⟩]

theorem sign_implies : sContract.Implies (Spec.Dsa.signContract abi) := by
  sig_implies [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, sContract, sRes, stackArgs_three,
    List.append_eq, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts, List.filterMap_cons,
    List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false, List.cons_append,
    List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append, pairFacts_three, List.range, List.range.loop]
    [signSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using signSatState

end VG.Proof.Dsa.PPC64LE
