module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Params.Front
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Dsa.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Dsa.Contract

/-!
# `vg_dsa_check_parameters` on PPC64LE: the contract on the registers

`checkParameters_implies`: `pcContract` implies the shared contract.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Impl.Dsa.PPC64LE

/-- A state meeting `pcContract.pre`: 1024-bit p and 160-bit q, the domain at
`0x1000` and the working space at `0x10000`. -/
def paramsSatState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 276 | .r5 => 128 | .r6 => 20 | .r7 => 0x10000 | .r8 => 2048 | _ => 0
  lr := 0
  sp := 0x9000
  mem _ := 0
  rd := [⟨0x1000, 276⟩]
  wr := [⟨0x10000, 16384⟩]

theorem checkParameters_implies : pcContract.Implies (Proof.Dsa.checkParametersContract abi) := by
  sig_implies [Proof.Dsa.checkParametersContract, Proof.Dsa.checkParametersSig, abi, argRegs, pcContract,
    List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts, List.filterMap_cons,
    List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false, List.cons_append,
    List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append]
    [paramsSatState] using paramsSatState

end VG.Proof.Dsa.PPC64LE
