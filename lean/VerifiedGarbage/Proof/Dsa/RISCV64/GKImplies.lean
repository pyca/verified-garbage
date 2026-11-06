module

public import VerifiedGarbage.Proof.Dsa.RISCV64.GKCtx
import VerifiedGarbage.Proof.Dsa.RISCV64.GKFn
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# `vg_dsa_generate_key` on RISC-V: the contract on the registers and the stack

As on PPC64LE (`Proof/Dsa/PPC64LE/Generate/Contract.lean`).
`generate_implies`: `gkContract` implies the shared contract, with
`gkStack` bytes of stack.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.Impl.Dsa.RISCV64
open VG.Proof.Dsa.RISCV64.GK

theorem gkStackArgs_three (s : State) :
    List.map (stackArg s) (List.range 3) = [stackArg s 0, stackArg s 1, stackArg s 2] :=
  rfl

/-- A state meeting `gkContract.pre`: 1024-bit p and 160-bit q, `out` at
`0x4000`, `used` at `0x5000`, the domain at `0x1000`, the tape at `0x6000`
and the working space at `0x10000`; the stack's arguments at `0x9000`. -/
def gkSatState : State where
  gpr r := match r with
    | .a0 => 0x4000 | .a1 => 424 | .a2 => 0x5000 | .a3 => 0x1000 | .a4 => 276 | .a5 => 128 | .a6 => 20
    | .a7 => 0x6000 | _ => 0
  sp := 0x9000
  mem a := bif Nat.beq a.toNat 0x900A then 0x01 else bif Nat.beq a.toNat 0x9011 then 0x24 else 0
  rd := [⟨0x1000, 276⟩, ⟨0x6000, 0⟩, ⟨0x9000, 24⟩]
  wr := [⟨0x4000, 424⟩, ⟨0x5000, 8⟩, ⟨0x10000, 73728⟩]

theorem generate_implies : gkContract.Implies (Spec.Dsa.generateKeyContract RISCV64.abi gkStack) := by
  exact
    { pre := by
        intro s h
        sig_pre [Spec.Dsa.generateKeyContract, Spec.Dsa.generateKeySig, RISCV64.abi, RISCV64.argRegs, gkContract, gkRes,
      gkStackArgs_three, List.append_eq, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts,
      List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false,
      List.cons_append, List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append, stackBelow] at h
        sig_split h
        have hx : Sig.conj (Sig.pairFacts [(⟨s.gpr .a7, (stackArg s 0).toNat⟩, false),
            (⟨stackArg s 1, (stackArg s 2).toNat * 8⟩, true), (⟨stackArgAddr s 0, 24⟩, false)]) := by
          with_reducible assumption
        simp only [Sig.pairFacts, List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false,
          Bool.or_false, Bool.false_or, List.nil_append, List.cons_append, Sig.conj_cons,
          Sig.conj] at hx
        obtain ⟨_, _⟩ := hx
        sig_reduce [Spec.Dsa.generateKeyContract, Spec.Dsa.generateKeySig, RISCV64.abi, RISCV64.argRegs, gkContract, gkRes,
      gkStackArgs_three, List.append_eq, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts,
      List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false,
      List.cons_append, List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append, stackBelow]
        sig_simp [Spec.Dsa.generateKeyContract, Spec.Dsa.generateKeySig, RISCV64.abi, RISCV64.argRegs, gkContract, gkRes,
      gkStackArgs_three, List.append_eq, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts,
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
      post := by sig_implies_post [Spec.Dsa.generateKeyContract, Spec.Dsa.generateKeySig, RISCV64.abi, RISCV64.argRegs, gkContract, gkRes,
      gkStackArgs_three, List.append_eq, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts,
      List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false,
      List.cons_append, List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append, stackBelow]
      pub := by sig_implies_pub [Spec.Dsa.generateKeyContract, Spec.Dsa.generateKeySig, RISCV64.abi, RISCV64.argRegs, gkContract, gkRes,
      gkStackArgs_three, List.append_eq, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts,
      List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false,
      List.cons_append, List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append, stackBelow]
      sat := by sig_implies_sat [Spec.Dsa.generateKeyContract, Spec.Dsa.generateKeySig, RISCV64.abi, RISCV64.argRegs, gkContract, gkRes,
      gkStackArgs_three, List.append_eq, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts,
      List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false,
      List.cons_append, List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append, stackBelow]
          [gkSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using gkSatState }

end VG.Proof.Dsa.RISCV64
