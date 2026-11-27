module

public import VerifiedGarbage.Proof.Ffdh.RISCV64.Derive.Body
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ffdh.RISCV64.Derive.Correct
import VerifiedGarbage.Proof.Ffdh.RISCV64.Derive.CT
public import VerifiedGarbage.Impl.Ffdh.RISCV64.Derive
public import VerifiedGarbage.Spec.Ffdh.DerivePublicContract
public import VerifiedGarbage.TCB.RISCV64.Target

/-!
# `vg_ffdh_derive_public` on RISC-V: verified against the shared contract

`dpContract` states the shared contract on the registers and the stack
(`dp_implies`); with correctness (`dp_correct`) and constant time (`dp_ct`),
`derivePublic` is verified (`derivePublic_verified`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64.Derive

open VG VG.RISCV64

theorem dpStackArgs_one (s : State) : List.map (stackArg s) (List.range 1) = [stackArg s 0] := rfl

/-- A state meeting `dpContract.pre`: a 512-bit p without q, `y` at `0x1000`,
the domain at `0x2000`, x at `0x3000`, the working space at `0x4000`, and the
stack argument at `0x9000`. -/
def dpSatState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 64 | .a2 => 0x2000 | .a3 => 128 | .a4 => 64 | .a5 => 0x3000 | .a6 => 1
    | .a7 => 0x4000 | _ => 0
  sp := 0x9000
  mem a := bif Nat.beq a.toNat 0x9000 then 0x20 else bif Nat.beq a.toNat 0x9001 then 0x04 else 0
  rd := [⟨0x2000, 128⟩, ⟨0x3000, 1⟩, ⟨0x9000, 8⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x4000, 8448⟩]

theorem dp_implies : dpContract.Implies (Spec.Ffdh.derivePublicContract RISCV64.abi) where
  pre := by
    intro s h
    sig_pre [Spec.Ffdh.derivePublicContract, Spec.Ffdh.derivePublicSig, RISCV64.abi, RISCV64.argRegs, dpContract,
      dpStackArgs_one, List.getD_cons_succ, List.getD_cons_zero, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid,
      List.append_eq, List.filter_cons, List.filter_nil, List.map_cons, List.map_nil, List.filterMap_cons,
      List.filterMap_nil, Sig.pairFacts, Sig.conj_cons, Sig.conj_append, List.cons_append, List.nil_append,
      List.append_nil, Bool.not_true, Bool.not_false, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false] at h
    sig_split h
    sig_reduce [Spec.Ffdh.derivePublicContract, Spec.Ffdh.derivePublicSig, RISCV64.abi, RISCV64.argRegs, dpContract,
      dpStackArgs_one, List.getD_cons_succ, List.getD_cons_zero, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid,
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
         simp_all only [dpStack])
  post := by
    sig_implies_post [Spec.Ffdh.derivePublicContract, Spec.Ffdh.derivePublicSig, RISCV64.abi, RISCV64.argRegs,
      dpContract, dpStackArgs_one, List.getD_cons_succ, List.getD_cons_zero]
  pub := by
    sig_implies_pub [Spec.Ffdh.derivePublicContract, Spec.Ffdh.derivePublicSig, RISCV64.abi, RISCV64.argRegs,
      dpContract, dpStackArgs_one, dpLeak, List.getD_cons_succ, List.getD_cons_zero]
  sat := by
    sig_implies_sat [Spec.Ffdh.derivePublicContract, Spec.Ffdh.derivePublicSig, RISCV64.abi, RISCV64.argRegs,
      dpContract, dpStackArgs_one, List.append_eq, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts,
      List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false,
      List.cons_append, List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append, Spec.Ffdh.pLenValid,
      Spec.Ffdh.domainLenValid] [dpSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using dpSatState

/-- `vg_ffdh_derive_public`. -/
theorem derivePublic_verified :
    Verified RISCV64.target Impl.Ffdh.RISCV64.Derive.derivePublic (Spec.Ffdh.derivePublicContract RISCV64.abi 0) :=
  Verified.of_correct dp_correct dp_ct dp_implies

end VG.Proof.Ffdh.RISCV64.Derive
