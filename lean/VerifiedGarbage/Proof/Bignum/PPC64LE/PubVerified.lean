module

import VerifiedGarbage.Proof.Bignum.PPC64LE.PubCT
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubCorrect
public import VerifiedGarbage.Proof.Bignum.PPC64LE.PubFn
public import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMid
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# `vg_rsa_public_precomputed_checked` on PPC64LE: verified against the shared contract

`fnContract` states the shared contract on the registers and the stack
(`publicChecked_implies`); with correctness (`fn_correct`) and constant time
(`fn_ct`), `publicChecked` is verified (`publicChecked_verified`).
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Pub

open VG VG.PPC64LE VG.Impl.Bignum.PPC64LE.PublicChecked

theorem stackArgs_two (s : State) : List.map (stackArg s) (List.range 2) = [stackArg s 0, stackArg s 1] := rfl

theorem pairFacts_two (a b : Region) : Sig.conj (Sig.pairFacts [(a, true), (b, false)]) ↔ a.Disjoint b := by
  simp [Sig.pairFacts, Sig.conj]

/-- A state meeting `fnContract.pre`: a 512-bit modulus, `out` at `0x1000`,
`pre` at `0x2000`, `e` at `0x3000`, the input at `0x3100` and the working
space at `0x4000`, its address and size on the stack at `0x9060`. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 64 | .r5 => 0x2000 | .r6 => 16 | .r7 => 0x3000 | .r8 => 1 | .r9 => 0x3100
    | .r10 => 64 | _ => 0
  lr := 0
  sp := 0x9000
  mem a := bif Nat.beq a.toNat 0x9061 then 0x40 else bif Nat.beq a.toNat 0x9068 then 0x70 else 0
  rd := [⟨0x2000, 128⟩, ⟨0x3000, 1⟩, ⟨0x3100, 64⟩, ⟨0x9060, 16⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x4000, 896⟩]

theorem publicChecked_implies : fnContract.Implies (Spec.Rsa.publicPrecomputedCheckedContract abi) := by
  sig_implies [Spec.Rsa.publicPrecomputedCheckedContract, Spec.Rsa.publicPrecomputedSig, abi, argRegs,
    fnContract, stackArgs_two, List.append_eq, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts,
    List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false,
    List.cons_append, List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append, pairFacts_two]
    [satState, stackArg, stackArgAddr, Mem.readW, Mem.read] using satState

/-- `vg_rsa_public_precomputed_checked`. -/
theorem publicChecked_verified :
    Verified target publicChecked (Spec.Rsa.publicPrecomputedCheckedContract abi) :=
  Verified.of_correct fn_correct fn_ct publicChecked_implies

end VG.Proof.Bignum.PPC64LE.Pub
