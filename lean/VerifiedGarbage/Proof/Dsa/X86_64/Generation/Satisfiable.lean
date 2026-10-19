module
public import Mathlib.Data.Int.ModEq
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.Slots
public import VerifiedGarbage.Proof.RsaKeyGen.Table
public import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
public import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
public import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit
public import VerifiedGarbage.Spec.Dsa.Generate
public import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ABI


/-! # The native parameter-generation contract admits concrete inputs -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64

def generationSatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 276 | .rdx => 128 | .rcx => 20
    | .r8 => 0x2000 | .rsp => 0x1000000000000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x1000000000009 then 0x30 else if a = 0x1000000000019 then 0x40
    else if a = 0x100000000002a then 1 else if a = 0x1000000000031 then 0x24 else 0
  rd := [⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x4000, 0⟩, ⟨0x1000000000008, 48⟩]
  wr := [⟨0x1000, 276⟩, ⟨0x10000, 73728⟩]

private theorem sat_arg_0 : stackArg generationSatState 0 = 0x3000 := by decide +kernel
private theorem sat_arg_1 : stackArg generationSatState 1 = 0 := by decide +kernel
private theorem sat_arg_2 : stackArg generationSatState 2 = 0x4000 := by decide +kernel
private theorem sat_arg_3 : stackArg generationSatState 3 = 0 := by decide +kernel
private theorem sat_arg_4 : stackArg generationSatState 4 = 0x10000 := by decide +kernel
private theorem sat_arg_5 : stackArg generationSatState 5 = 9216 := by decide +kernel

theorem generation_satisfiable : ∃ s, (Spec.Dsa.generateParametersContract abi 472).pre s := by
  refine ⟨generationSatState, ?_⟩
  sig_pre [Spec.Dsa.generateParametersContract, Spec.Dsa.generateParametersSig, abi, argRegs, stackArgs_six]
  sig_and_intros
  all_goals try simp only [sat_arg_0, sat_arg_1, sat_arg_2, sat_arg_3, sat_arg_4, sat_arg_5]
  all_goals first
    | exact Region.disjoint_of_sep (by decide +kernel)
    | decide +kernel
    | (intro a h₁ h₂; simp only [Region.Contains, stackArgAddr, generationSatState] at h₁ h₂; bv_omega)

end VG.Proof.Dsa.X86_64.Generation
