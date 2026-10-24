module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.GenerateKey.Fn
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# `vg_ffdh_generate_key` on PPC64LE: the shared contract

`gkContract` states the shared contract on the registers and the stack
(`gk_implies`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.GenerateKey

open VG VG.PPC64LE

theorem gkStackArgs_three (s : State) :
    List.map (stackArg s) (List.range 3) = [stackArg s 0, stackArg s 1, stackArg s 2] := rfl

/-- A state meeting `gkContract.pre`: a 512-bit p without q, x at `0x1000`,
`y` at `0x1100`, the domain at `0x2000`, `rand` at `0x3000`, the working
space at `0x4000`, and the stack arguments at `0x9060`. -/
def gkSatState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 64 | .r5 => 0x1100 | .r6 => 64 | .r7 => 0x2000 | .r8 => 128 | .r9 => 64
    | .r10 => 0x3000 | _ => 0
  lr := 0
  sp := 0x9000
  mem a := bif Nat.beq a.toNat 0x9060 then 64 else bif Nat.beq a.toNat 0x9069 then 0x40 else
    bif Nat.beq a.toNat 0x9070 then 0x20 else bif Nat.beq a.toNat 0x9071 then 0x04 else 0
  rd := [⟨0x2000, 128⟩, ⟨0x3000, 64⟩, ⟨0x9060, 24⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1100, 64⟩, ⟨0x4000, 8448⟩]

theorem gk_implies : gkContract.Implies (Spec.Ffdh.generateKeyContract abi) where
  pre := by
    intro s h
    sig_pre [Spec.Ffdh.generateKeyContract, Spec.Ffdh.generateKeySig, abi, argRegs, gkContract,
      gkStackArgs_three, List.getD_cons_succ, List.getD_cons_zero, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid,
      List.append_eq, List.filter_cons, List.filter_nil, List.map_cons, List.map_nil, List.filterMap_cons,
      List.filterMap_nil, Sig.pairFacts, Sig.conj_cons, Sig.conj_append, List.cons_append, List.nil_append,
      List.append_nil, Bool.not_true, Bool.not_false, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false] at h
    sig_split h
    sig_reduce [Spec.Ffdh.generateKeyContract, Spec.Ffdh.generateKeySig, abi, argRegs, gkContract,
      gkStackArgs_three, List.getD_cons_succ, List.getD_cons_zero, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid,
      List.append_eq, List.filter_cons, List.filter_nil, List.map_cons, List.map_nil, List.filterMap_cons,
      List.filterMap_nil, Sig.pairFacts, Sig.conj_cons, Sig.conj_append, List.cons_append, List.nil_append,
      List.append_nil, Bool.not_true, Bool.not_false, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false]
    sig_simp [Spec.Ffdh.generateKeyContract, Spec.Ffdh.generateKeySig, abi, argRegs, gkContract,
      gkStackArgs_three, List.getD_cons_succ, List.getD_cons_zero, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid,
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
      | (simp only [Sig.pairFacts, List.filterMap_cons, List.filterMap_nil, Bool.or_true, Bool.or_false,
          Bool.cond_true, Bool.cond_false, Sig.conj_cons, List.nil_append, List.cons_append] at *
         simp_all only [gkStack])
  post := by
    sig_implies_post [Spec.Ffdh.generateKeyContract, Spec.Ffdh.generateKeySig, abi, argRegs, gkContract,
      gkStackArgs_three, List.getD_cons_succ, List.getD_cons_zero]
  pub := by
    sig_implies_pub [Spec.Ffdh.generateKeyContract, Spec.Ffdh.generateKeySig, abi, argRegs, gkContract,
      gkStackArgs_three, gkLeak, gkScalar, List.getD_cons_succ, List.getD_cons_zero]
  sat := by
    sig_implies_sat [Spec.Ffdh.generateKeyContract, Spec.Ffdh.generateKeySig, abi, argRegs, gkContract,
      gkStackArgs_three, List.append_eq, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts,
      List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false,
      List.cons_append, List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append, Spec.Ffdh.pLenValid,
      Spec.Ffdh.domainLenValid] [gkSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using gkSatState

end VG.Proof.Ffdh.PPC64LE.GenerateKey
