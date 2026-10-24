module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Derive.Fn
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# `vg_ffdh_derive_public` on PPC64LE: the shared contract

`dpContract` states the shared contract on the registers and the stack
(`dp_implies`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Derive

open VG VG.PPC64LE

theorem dpStackArgs_one (s : State) : List.map (stackArg s) (List.range 1) = [stackArg s 0] := rfl

/-- A state meeting `dpContract.pre`: a 512-bit p without q, `y` at `0x1000`,
the domain at `0x2000`, x at `0x3000`, the working space at `0x4000`, and
the stack argument at `0x9060`. -/
def dpSatState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 64 | .r5 => 0x2000 | .r6 => 128 | .r7 => 64 | .r8 => 0x3000 | .r9 => 1
    | .r10 => 0x4000 | _ => 0
  lr := 0
  sp := 0x9000
  mem a := bif Nat.beq a.toNat 0x9060 then 0x20 else bif Nat.beq a.toNat 0x9061 then 0x04 else 0
  rd := [⟨0x2000, 128⟩, ⟨0x3000, 1⟩, ⟨0x9060, 8⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x4000, 8448⟩]

theorem dp_implies : dpContract.Implies (Spec.Ffdh.derivePublicContract abi) where
  pre := by
    intro s h
    sig_pre [Spec.Ffdh.derivePublicContract, Spec.Ffdh.derivePublicSig, abi, argRegs, dpContract,
      dpStackArgs_one, List.getD_cons_succ, List.getD_cons_zero, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid,
      List.append_eq, List.filter_cons, List.filter_nil, List.map_cons, List.map_nil, List.filterMap_cons,
      List.filterMap_nil, Sig.pairFacts, Sig.conj_cons, Sig.conj_append, List.cons_append, List.nil_append,
      List.append_nil, Bool.not_true, Bool.not_false, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false] at h
    sig_split h
    sig_reduce [Spec.Ffdh.derivePublicContract, Spec.Ffdh.derivePublicSig, abi, argRegs, dpContract,
      dpStackArgs_one, List.getD_cons_succ, List.getD_cons_zero, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid,
      List.append_eq, List.filter_cons, List.filter_nil, List.map_cons, List.map_nil, List.filterMap_cons,
      List.filterMap_nil, Sig.pairFacts, Sig.conj_cons, Sig.conj_append, List.cons_append, List.nil_append,
      List.append_nil, Bool.not_true, Bool.not_false, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false]
    sig_simp [Spec.Ffdh.derivePublicContract, Spec.Ffdh.derivePublicSig, abi, argRegs, dpContract,
      dpStackArgs_one, List.getD_cons_succ, List.getD_cons_zero, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid,
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
         simp_all only [dpStack])
  post := by
    sig_implies_post [Spec.Ffdh.derivePublicContract, Spec.Ffdh.derivePublicSig, abi, argRegs, dpContract,
      dpStackArgs_one, List.getD_cons_succ, List.getD_cons_zero]
  pub := by
    sig_implies_pub [Spec.Ffdh.derivePublicContract, Spec.Ffdh.derivePublicSig, abi, argRegs, dpContract,
      dpStackArgs_one, dpLeak, List.getD_cons_succ, List.getD_cons_zero]
  sat := by
    sig_implies_sat [Spec.Ffdh.derivePublicContract, Spec.Ffdh.derivePublicSig, abi, argRegs, dpContract,
      dpStackArgs_one, List.append_eq, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts,
      List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false,
      List.cons_append, List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append, Spec.Ffdh.pLenValid,
      Spec.Ffdh.domainLenValid] [dpSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using dpSatState

end VG.Proof.Ffdh.PPC64LE.Derive
