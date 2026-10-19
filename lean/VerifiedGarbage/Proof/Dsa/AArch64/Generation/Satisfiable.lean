module
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Proof.Dsa.AArch64.Run
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.Table
public import VerifiedGarbage.Spec.Dsa.Generate
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ABI


/-! Concrete public inputs satisfy the parameter-generation contract. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64

def generationSatState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 276 | .x2 => 128 | .x3 => 20
    | .x4 => 0x2000 | .x6 => 0x3000 | _ => 0
  sp := 0x1000000000000
  mem a := if a = 0x1000000000001 then 0x40 else if a = 0x1000000000012 then 1
    else if a = 0x1000000000019 then 0x24 else 0
  rd := [⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x4000, 0⟩, ⟨0x1000000000000, 32⟩]
  wr := [⟨0x1000, 276⟩, ⟨0x10000, 73728⟩]

private theorem sat_arg_0 : stackArg generationSatState 0 = 0x4000 := by decide +kernel
private theorem sat_arg_1 : stackArg generationSatState 1 = 0 := by decide +kernel
private theorem sat_arg_2 : stackArg generationSatState 2 = 0x10000 := by decide +kernel
private theorem sat_arg_3 : stackArg generationSatState 3 = 9216 := by decide +kernel

theorem generation_satisfiable : ∃ s, (Spec.Dsa.generateParametersContract abi 464).pre s := by
  refine ⟨generationSatState, ?_⟩
  sig_pre [Spec.Dsa.generateParametersContract, Spec.Dsa.generateParametersSig, abi, argRegs, generationStackArgs]
  sig_and_intros
  all_goals try simp only [sat_arg_0, sat_arg_1, sat_arg_2, sat_arg_3]
  all_goals first
    | exact Region.disjoint_of_sep (by decide +kernel)
    | decide +kernel
    | (intro a h₁ h₂; simp only [Region.Contains, stackArgAddr, generationSatState] at h₁ h₂; bv_omega)

end VG.Proof.Dsa.AArch64.Generation
