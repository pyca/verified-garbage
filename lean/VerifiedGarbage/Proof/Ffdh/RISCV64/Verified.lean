module

public import VerifiedGarbage.Proof.Ffdh.RISCV64.Fn
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ffdh.RISCV64.Correct
import VerifiedGarbage.Proof.Ffdh.RISCV64.CT
public import VerifiedGarbage.Impl.Ffdh.RISCV64
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.TCB.RISCV64.Target

/-!
# `vg_ffdh_exchange` on RISC-V: verified against the shared contract

`fnContract` states the shared contract on the registers and the stack
(`ex_implies`); with correctness (`fn_correct`) and constant time
(`ex_ct`), `exchange` is verified (`exchange_verified`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64

open VG VG.RISCV64

theorem stackArgs_three (s : State) :
    List.map (stackArg s) (List.range 3) = [stackArg s 0, stackArg s 1, stackArg s 2] := rfl

/-- A state meeting `fnContract.pre`: a 512-bit p without q, `out` at
`0x1000`, the domain at `0x2000`, x at `0x3000`, the peer at `0x3100`, the
working space at `0x4000`, and the stack arguments at `0x9000`. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 64 | .a2 => 0x2000 | .a3 => 128 | .a4 => 64 | .a5 => 0x3000 | .a6 => 1
    | .a7 => 0x3100 | _ => 0
  sp := 0x9000
  mem a := bif Nat.beq a.toNat 0x9000 then 64 else bif Nat.beq a.toNat 0x9009 then 0x40 else
    bif Nat.beq a.toNat 0x9010 then 0x20 else bif Nat.beq a.toNat 0x9011 then 0x04 else 0
  rd := [⟨0x2000, 128⟩, ⟨0x3000, 1⟩, ⟨0x3100, 64⟩, ⟨0x9000, 24⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x4000, 8448⟩]

theorem ex_implies : fnContract.Implies (Spec.Ffdh.exchangeContract RISCV64.abi) where
  pre := by
    intro s h
    sig_pre [Spec.Ffdh.exchangeContract, Spec.Ffdh.exchangeSig, RISCV64.abi, RISCV64.argRegs, fnContract,
      stackArgs_three, List.getD_cons_succ, List.getD_cons_zero, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid,
      List.append_eq, List.filter_cons, List.filter_nil, List.map_cons, List.map_nil, List.filterMap_cons,
      List.filterMap_nil, Sig.pairFacts, Sig.conj_cons, Sig.conj_append, List.cons_append, List.nil_append,
      List.append_nil, Bool.not_true, Bool.not_false, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false] at h
    sig_split h
    sig_reduce [Spec.Ffdh.exchangeContract, Spec.Ffdh.exchangeSig, RISCV64.abi, RISCV64.argRegs, fnContract,
      stackArgs_three, List.getD_cons_succ, List.getD_cons_zero, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid,
      List.append_eq, List.filter_cons, List.filter_nil, List.map_cons, List.map_nil, List.filterMap_cons,
      List.filterMap_nil, Sig.pairFacts, Sig.conj_cons, Sig.conj_append, List.cons_append, List.nil_append,
      List.append_nil, Bool.not_true, Bool.not_false, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | sig_disjoint_symm
      | omega
      | (sig_simp_only [Nat.mul_comm] at *
         first | with_reducible assumption | sig_disjoint_symm)
      | (simp only [Sig.pairFacts, List.filterMap_cons, List.filterMap_nil, Bool.or_true, Bool.or_false,
          Bool.cond_true, Bool.cond_false, Sig.conj_cons, List.nil_append, List.cons_append] at *
         simp_all only [stackArgs])
  post := by
    sig_implies_post [Spec.Ffdh.exchangeContract, Spec.Ffdh.exchangeSig, RISCV64.abi, RISCV64.argRegs, fnContract,
      stackArgs_three, List.getD_cons_succ, List.getD_cons_zero]
  pub := by
    sig_implies_pub [Spec.Ffdh.exchangeContract, Spec.Ffdh.exchangeSig, RISCV64.abi, RISCV64.argRegs, fnContract,
      stackArgs_three, exLeak, List.getD_cons_succ, List.getD_cons_zero]
  sat := by
    sig_implies_sat [Spec.Ffdh.exchangeContract, Spec.Ffdh.exchangeSig, RISCV64.abi, RISCV64.argRegs, fnContract,
      stackArgs_three, List.append_eq, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts,
      List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false,
      List.cons_append, List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append, Spec.Ffdh.pLenValid,
      Spec.Ffdh.domainLenValid] [satState, stackArg, stackArgAddr, Mem.readW, Mem.read] using satState

end VG.Proof.Ffdh.RISCV64

/-! ## Verified -/

namespace VG.Proof.Ffdh.RISCV64

open VG VG.RISCV64

/-- `vg_ffdh_exchange`. -/
theorem exchange_verified :
    Verified RISCV64.target Impl.Ffdh.RISCV64.exchange (Spec.Ffdh.exchangeContract RISCV64.abi 0) :=
  Verified.of_correct fn_correct ex_ct ex_implies

end VG.Proof.Ffdh.RISCV64
