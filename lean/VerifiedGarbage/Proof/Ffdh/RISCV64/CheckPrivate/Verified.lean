module

public import VerifiedGarbage.Proof.Ffdh.RISCV64.CheckPrivate.Body
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ffdh.RISCV64.CheckPrivate.Correct
import VerifiedGarbage.Proof.Ffdh.RISCV64.CheckPrivate.CT
public import VerifiedGarbage.Impl.Ffdh.RISCV64.CheckPrivate
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.TCB.RISCV64.Target

/-!
# `vg_ffdh_check_private` on RISC-V: verified against the shared contract

`kpContract` states the shared contract on the registers and the stack
(`kp_implies`); with correctness (`kp_correct`) and constant time (`kp_ct`),
`checkPrivate` is verified (`checkPrivate_verified`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64.CheckPrivate

open VG VG.RISCV64

theorem kpStackArgs_one (s : State) : List.map (stackArg s) (List.range 1) = [stackArg s 0] := rfl

/-- A state meeting `kpContract.pre`: a 512-bit p without q, the domain at
`0x2000`, y at `0x3100`, x at `0x3000`, the working space at `0x4000`, and the
stack argument at `0x9000`. -/
def kpSatState : State where
  gpr r := match r with
    | .a0 => 0x2000 | .a1 => 128 | .a2 => 64 | .a3 => 0x3100 | .a4 => 64 | .a5 => 0x3000 | .a6 => 1
    | .a7 => 0x4000 | _ => 0
  sp := 0x9000
  mem a := bif Nat.beq a.toNat 0x9000 then 0x20 else bif Nat.beq a.toNat 0x9001 then 0x04 else 0
  rd := [⟨0x2000, 128⟩, ⟨0x3100, 64⟩, ⟨0x3000, 1⟩, ⟨0x9000, 8⟩]
  wr := [⟨0x4000, 8448⟩]

theorem kp_implies : kpContract.Implies (Spec.Ffdh.checkPrivateContract RISCV64.abi) where
  pre := by
    intro s h
    sig_pre [Spec.Ffdh.checkPrivateContract, Spec.Ffdh.checkPrivateSig, RISCV64.abi, RISCV64.argRegs, kpContract,
      kpStackArgs_one, List.getD_cons_succ, List.getD_cons_zero, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid,
      List.append_eq, List.filter_cons, List.filter_nil, List.map_cons, List.map_nil, List.filterMap_cons,
      List.filterMap_nil, Sig.pairFacts, Sig.conj_cons, Sig.conj_append, List.cons_append, List.nil_append,
      List.append_nil, Bool.not_true, Bool.not_false, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false] at h
    sig_split h
    sig_reduce [Spec.Ffdh.checkPrivateContract, Spec.Ffdh.checkPrivateSig, RISCV64.abi, RISCV64.argRegs, kpContract,
      kpStackArgs_one, List.getD_cons_succ, List.getD_cons_zero, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid,
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
      | (simp only [Sig.pairFacts, List.filterMap_cons, List.filterMap_nil, Bool.or_false,
          Bool.cond_true, Sig.conj_cons, List.nil_append, List.cons_append] at *
         simp_all only [kpStack])
  post := by
    sig_implies_post [Spec.Ffdh.checkPrivateContract, Spec.Ffdh.checkPrivateSig, RISCV64.abi, RISCV64.argRegs,
      kpContract, kpStackArgs_one, List.getD_cons_succ, List.getD_cons_zero]
  pub := by
    sig_implies_pub [Spec.Ffdh.checkPrivateContract, Spec.Ffdh.checkPrivateSig, RISCV64.abi, RISCV64.argRegs,
      kpContract, kpStackArgs_one, kpLeak, kpStatus, List.getD_cons_succ, List.getD_cons_zero]
  sat := by
    sig_implies_sat [Spec.Ffdh.checkPrivateContract, Spec.Ffdh.checkPrivateSig, RISCV64.abi, RISCV64.argRegs,
      kpContract, kpStackArgs_one, List.append_eq, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts,
      List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false,
      List.cons_append, List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append, Spec.Ffdh.pLenValid,
      Spec.Ffdh.domainLenValid] [kpSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using kpSatState

/-- `vg_ffdh_check_private`. -/
theorem checkPrivate_verified :
    Verified RISCV64.target Impl.Ffdh.RISCV64.CheckPrivate.checkPrivate (Spec.Ffdh.checkPrivateContract RISCV64.abi 0) :=
  Verified.of_correct kp_correct kp_ct kp_implies

end VG.Proof.Ffdh.RISCV64.CheckPrivate
