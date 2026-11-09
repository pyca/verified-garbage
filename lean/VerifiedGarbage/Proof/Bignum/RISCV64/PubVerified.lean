module

public import VerifiedGarbage.Proof.Bignum.RISCV64.PubCT
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Rsa.Contract
meta import VerifiedGarbage.Proof.Rsa.Contract

/-! # `vg_rsa_public_precomputed_checked` on RISC-V -/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64.Pub

open VG VG.RISCV64 VG.Impl.Bignum.RISCV64.PublicChecked

theorem stackArgs_two (s : State) :
    List.map (stackArg s) (List.range 2) = [stackArg s 0, stackArg s 1] := rfl

theorem pairFacts_two (a b : Region) :
    Sig.conj (Sig.pairFacts [(a, true), (b, false)]) ↔ a.Disjoint b := by
  simp [Sig.pairFacts, Sig.conj]

/-- A state meeting `fnContract.pre`: a 512-bit modulus, `pre` at `0x2000`,
`e`'s one byte at `0x3000`, the input at `0x3100`, the output at
`0x1000`, and on the stack the working space at `0x4000` and its 112 words. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 64 | .a2 => 0x2000 | .a3 => 16 | .a4 => 0x3000 | .a5 => 1 | .a6 => 0x3100
    | .a7 => 64 | _ => 0
  sp := 0x9000
  mem a := bif Nat.beq a.toNat 0x9001 then 0x40 else bif Nat.beq a.toNat 0x9008 then 0x70 else 0
  rd := [⟨0x2000, 128⟩, ⟨0x3000, 1⟩, ⟨0x3100, 64⟩, ⟨0x9000, 16⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x4000, 896⟩]

theorem publicChecked_implies :
    fnContract.Implies (Proof.Rsa.publicPrecomputedCheckedContract RISCV64.abi) := by
  sig_implies [Proof.Rsa.publicPrecomputedCheckedContract, Proof.Rsa.publicPrecomputedSig, RISCV64.abi,
    RISCV64.argRegs, fnContract, stackArgs_two, List.append_eq, List.getD_cons_succ, List.getD_cons_zero,
    Sig.pairFacts, List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true,
    Bool.or_false, List.cons_append, List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append,
    pairFacts_two, List.range, List.range.loop]
    [satState, stackArg, stackArgAddr, Mem.readW, Mem.read] using satState

/-- `vg_rsa_public_precomputed_checked`. -/
theorem publicChecked_verified :
    Verified RISCV64.target publicChecked (Proof.Rsa.publicPrecomputedCheckedContract RISCV64.abi) :=
  Verified.of_correct fn_correct fn_ct publicChecked_implies

end VG.Proof.Bignum.RISCV64.Pub
