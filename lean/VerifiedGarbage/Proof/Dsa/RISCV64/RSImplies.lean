module

public import VerifiedGarbage.Proof.Dsa.RISCV64.RSCtx
import VerifiedGarbage.Proof.Dsa.RISCV64.RSFn
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# `vg_dsa_sign_random` on RISC-V: the contract on the registers and the stack

As on PPC64LE (`Proof/Dsa/PPC64LE/RandomSign/Contract.lean`).
`randomSign_implies`: `rsContract` implies the shared contract, with
`rsStack` bytes of stack; `randomSign_wp`: `vg_dsa_sign_random` meets the
shared contract's precondition and postcondition, and the calling
convention.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.Impl.Dsa.RISCV64
open VG.Proof.Dsa.RISCV64.RS

theorem rsStackArgs_five (s : State) :
    List.map (stackArg s) (List.range 5) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4] :=
  rfl

/-- A state meeting `rsContract.pre`: 1024-bit p and 160-bit q, `out` at
`0x4000`, `used` at `0x5000`, the key at `0x1000`, the digest at `0x3000`,
the tape at `0x6000` and the working space at `0x10000`; the stack's
arguments at `0x9000`. -/
def rsSatState : State where
  gpr r := match r with
    | .a0 => 0x4000 | .a1 => 40 | .a2 => 0x5000 | .a3 => 0x1000 | .a4 => 424 | .a5 => 128 | .a6 => 20
    | .a7 => 0x3000 | _ => 0
  sp := 0x9000
  mem a := bif Nat.beq a.toNat 0x9009 then 0x60 else bif Nat.beq a.toNat 0x901A then 0x01 else
    bif Nat.beq a.toNat 0x9020 then 0x40 else bif Nat.beq a.toNat 0x9021 then 0x08 else 0
  rd := [⟨0x1000, 424⟩, ⟨0x3000, 0⟩, ⟨0x6000, 0⟩, ⟨0x9000, 40⟩]
  wr := [⟨0x4000, 40⟩, ⟨0x5000, 8⟩, ⟨0x10000, 16896⟩]

theorem randomSign_implies : rsContract.Implies (Spec.Dsa.randomSignContract RISCV64.abi rsStack) := by
  exact
    { pre := by
        intro s h
        sig_pre [Spec.Dsa.randomSignContract, Spec.Dsa.randomSignSig, RISCV64.abi, RISCV64.argRegs, rsContract, rsRes,
      rsStackArgs_five, List.append_eq, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts,
      List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false,
      List.cons_append, List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append, stackBelow] at h
        sig_split h
        have hx : Sig.conj (Sig.pairFacts [(⟨s.gpr .a7, (stackArg s 0).toNat⟩, false),
            (⟨stackArg s 1, (stackArg s 2).toNat⟩, false), (⟨stackArg s 3, (stackArg s 4).toNat * 8⟩, true),
            (⟨stackArgAddr s 0, 40⟩, false)]) := by with_reducible assumption
        simp only [Sig.pairFacts, List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false,
          Bool.or_false, Bool.false_or, List.nil_append, List.cons_append, Sig.conj_cons,
          Sig.conj] at hx
        obtain ⟨_, _, _⟩ := hx
        sig_reduce [Spec.Dsa.randomSignContract, Spec.Dsa.randomSignSig, RISCV64.abi, RISCV64.argRegs, rsContract, rsRes,
      rsStackArgs_five, List.append_eq, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts,
      List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false,
      List.cons_append, List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append, stackBelow]
        sig_simp [Spec.Dsa.randomSignContract, Spec.Dsa.randomSignSig, RISCV64.abi, RISCV64.argRegs, rsContract, rsRes,
      rsStackArgs_five, List.append_eq, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts,
      List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false,
      List.cons_append, List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append, stackBelow] []
        sig_and_intros
        sig_close
        all_goals first
          | with_reducible assumption
          | sig_disjoint_symm
          | omega
          | skip
        all_goals done
      post := by sig_implies_post [Spec.Dsa.randomSignContract, Spec.Dsa.randomSignSig, RISCV64.abi, RISCV64.argRegs, rsContract, rsRes,
      rsStackArgs_five, List.append_eq, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts,
      List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false,
      List.cons_append, List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append, stackBelow]
      pub := by sig_implies_pub [Spec.Dsa.randomSignContract, Spec.Dsa.randomSignSig, RISCV64.abi, RISCV64.argRegs, rsContract, rsRes,
      rsStackArgs_five, List.append_eq, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts,
      List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false,
      List.cons_append, List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append, stackBelow]
      sat := by sig_implies_sat [Spec.Dsa.randomSignContract, Spec.Dsa.randomSignSig, RISCV64.abi, RISCV64.argRegs, rsContract, rsRes,
      rsStackArgs_five, List.append_eq, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts,
      List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false,
      List.cons_append, List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append, stackBelow]
          [rsSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using rsSatState }

/-- `vg_dsa_sign_random` under the shared contract. -/
theorem randomSign_wp (s : State) (h : (Spec.Dsa.randomSignContract RISCV64.abi rsStack).pre s) :
    WP isa RandomSign.code s fun t =>
      abiPreserved s t ∧ (Spec.Dsa.randomSignContract RISCV64.abi rsStack).post s t := by
  obtain ⟨tr, t, he, ha, hp⟩ := randomSign_correct s (randomSign_implies.pre s h)
  exact ⟨tr, t, he, ha, randomSign_implies.post s t h hp⟩

end VG.Proof.Dsa.RISCV64
