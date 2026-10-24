module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.CheckPrivate.Fn
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# `vg_ffdh_check_private` on PPC64LE: the shared contract

`kpContract` states the shared contract on the registers and the stack
(`kp_implies`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.CheckPrivate

open VG VG.PPC64LE

theorem kpStackArgs_one (s : State) : List.map (stackArg s) (List.range 1) = [stackArg s 0] := rfl

/-- A state meeting `kpContract.pre`: a 512-bit p without q, the domain at
`0x2000`, y at `0x1000`, x at `0x3000`, the working space at `0x4000`, and
the stack argument at `0x9060`. -/
def kpSatState : State where
  gpr r := match r with
    | .r3 => 0x2000 | .r4 => 128 | .r5 => 64 | .r6 => 0x1000 | .r7 => 64 | .r8 => 0x3000 | .r9 => 1
    | .r10 => 0x4000 | _ => 0
  lr := 0
  sp := 0x9000
  mem a := bif Nat.beq a.toNat 0x9060 then 0x20 else bif Nat.beq a.toNat 0x9061 then 0x04 else 0
  rd := [⟨0x2000, 128⟩, ⟨0x1000, 64⟩, ⟨0x3000, 1⟩, ⟨0x9060, 8⟩]
  wr := [⟨0x4000, 8448⟩]

theorem kp_implies : kpContract.Implies (Spec.Ffdh.checkPrivateContract abi) where
  pre := by
    intro s h
    sig_pre [Spec.Ffdh.checkPrivateContract, Spec.Ffdh.checkPrivateSig, abi, argRegs, kpContract,
      kpStackArgs_one, List.getD_cons_succ, List.getD_cons_zero, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid,
      List.append_eq, List.filter_cons, List.filter_nil, List.map_cons, List.map_nil, List.filterMap_cons,
      List.filterMap_nil, Sig.pairFacts, Sig.conj_cons, Sig.conj_append, List.cons_append, List.nil_append,
      List.append_nil, Bool.not_true, Bool.not_false, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false] at h
    sig_split h
    sig_reduce [Spec.Ffdh.checkPrivateContract, Spec.Ffdh.checkPrivateSig, abi, argRegs, kpContract,
      kpStackArgs_one, List.getD_cons_succ, List.getD_cons_zero, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid,
      List.append_eq, List.filter_cons, List.filter_nil, List.map_cons, List.map_nil, List.filterMap_cons,
      List.filterMap_nil, Sig.pairFacts, Sig.conj_cons, Sig.conj_append, List.cons_append, List.nil_append,
      List.append_nil, Bool.not_true, Bool.not_false, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false]
    sig_simp [Spec.Ffdh.checkPrivateContract, Spec.Ffdh.checkPrivateSig, abi, argRegs, kpContract,
      kpStackArgs_one, List.getD_cons_succ, List.getD_cons_zero, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid,
      List.append_eq, List.filter_cons, List.filter_nil, List.map_cons, List.map_nil, List.filterMap_cons,
      List.filterMap_nil, Sig.pairFacts, Sig.conj_cons, Sig.conj_append, List.cons_append, List.nil_append,
      List.append_nil, Bool.not_true, Bool.not_false, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false] []
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | sig_disjoint_symm
      | omega
      | (sig_simp_only [Nat.mul_comm] at *
         first | with_reducible assumption | sig_disjoint_symm)
      | (simp only [Sig.pairFacts, List.filterMap_cons, List.filterMap_nil, Bool.or_false, Bool.cond_true,
          Sig.conj_cons, List.nil_append, List.cons_append] at *
         simp_all only [kpStack])
  post := by
    sig_implies_post [Spec.Ffdh.checkPrivateContract, Spec.Ffdh.checkPrivateSig, abi, argRegs, kpContract,
      kpStackArgs_one, List.getD_cons_succ, List.getD_cons_zero]
  pub := by
    sig_implies_pub [Spec.Ffdh.checkPrivateContract, Spec.Ffdh.checkPrivateSig, abi, argRegs, kpContract,
      kpStackArgs_one, kpLeak, List.getD_cons_succ, List.getD_cons_zero]
  sat := by
    sig_implies_sat [Spec.Ffdh.checkPrivateContract, Spec.Ffdh.checkPrivateSig, abi, argRegs, kpContract,
      kpStackArgs_one, List.append_eq, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts,
      List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false,
      List.cons_append, List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append, Spec.Ffdh.pLenValid,
      Spec.Ffdh.domainLenValid] [kpSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using kpSatState

end VG.Proof.Ffdh.PPC64LE.CheckPrivate
