module

public import VerifiedGarbage.Proof.Dsa.RISCV64.ParamsFront
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Dsa.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Dsa.Contract
import VerifiedGarbage.Proof.Dsa.RISCV64.ParamsFn

/-!
# `vg_dsa_check_parameters` on RISC-V: the shared contract

`checkParameters_implies`: `pcContract` implies the shared contract;
`checkParameters_wp`: `vg_dsa_check_parameters` meets it, with no stack of
its own.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.Impl.Dsa.RISCV64

/-- A state meeting `pcContract.pre`: 1024-bit p and 160-bit q, the domain at
`0x1000` and the working space at `0x10000`. -/
def paramsSatState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 276 | .a2 => 128 | .a3 => 20 | .a4 => 0x10000 | .a5 => 2048 | _ => 0
  sp := 0x9000
  mem _ := 0
  rd := [⟨0x1000, 276⟩]
  wr := [⟨0x10000, 16384⟩]

theorem checkParameters_implies : pcContract.Implies (Proof.Dsa.checkParametersContract RISCV64.abi) := by
  sig_implies [Proof.Dsa.checkParametersContract, Proof.Dsa.checkParametersSig, RISCV64.abi, RISCV64.argRegs,
    pcContract, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts, List.filterMap_cons,
    List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false, List.cons_append,
    List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append]
    [paramsSatState] using paramsSatState

/-- `vg_dsa_check_parameters` under the shared contract. -/
theorem checkParameters_wp (s : State) (h : (Proof.Dsa.checkParametersContract RISCV64.abi).pre s) :
    WP isa Params.checkParameters s fun t =>
      abiPreserved s t ∧ (Proof.Dsa.checkParametersContract RISCV64.abi).post s t := by
  obtain ⟨tr, t, he, ha, hp⟩ := checkParameters_correct s (checkParameters_implies.pre s h)
  exact ⟨tr, t, he, ha, checkParameters_implies.post s t h hp⟩

end VG.Proof.Dsa.RISCV64
