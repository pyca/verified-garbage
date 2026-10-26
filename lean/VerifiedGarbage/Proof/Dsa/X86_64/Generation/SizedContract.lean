module

public import VerifiedGarbage.Spec.Dsa.GenerationSized
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ABI
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Proof.Framework.X86_64.Call
public import VerifiedGarbage.Spec.Dsa.Generate
public import VerifiedGarbage.TCB.X86_64.Target

/-! # The restricted helper adds only the public width precondition -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation.Sized
open VG VG.X86_64

theorem pre_of_sized {pBytes : Nat} {s : State}
    (h : (Spec.Dsa.GenerationSized.contract pBytes abi 472).pre s) :
    (Spec.Dsa.generateParametersContract abi 472).pre s := by
  sig_pre [Spec.Dsa.GenerationSized.contract, Spec.Dsa.generateParametersSig, abi, argRegs, stackArgs_six] at h
  sig_pre [Spec.Dsa.GenerationSized.contract, Spec.Dsa.generateParametersSig, abi, argRegs, stackArgs_six] at h
  sig_split h
  sig_pre [Spec.Dsa.generateParametersContract, Spec.Dsa.generateParametersSig, abi, argRegs, stackArgs_six]
  sig_pre [Spec.Dsa.generateParametersContract, Spec.Dsa.generateParametersSig, abi, argRegs, stackArgs_six]
  sig_and_intros
  all_goals with_reducible assumption

theorem width_of_sized {pBytes : Nat} {s : State}
    (h : (Spec.Dsa.GenerationSized.contract pBytes abi 472).pre s) :
    (s.gpr .rdx).toNat = pBytes := by
  sig_pre [Spec.Dsa.GenerationSized.contract, Spec.Dsa.generateParametersSig, abi, argRegs, stackArgs_six] at h
  sig_pre [Spec.Dsa.GenerationSized.contract, Spec.Dsa.generateParametersSig, abi, argRegs, stackArgs_six] at h
  sig_split h
  with_reducible assumption

def sizedSatState (pBytes : Nat) : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => BitVec.ofNat 64 (2 * pBytes + if pBytes = 128 then 20 else 32)
    | .rdx => BitVec.ofNat 64 pBytes | .rcx => if pBytes = 128 then 20 else 32
    | .r8 => 0x2000 | .rsp => 0x1000000000000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x1000000000009 then 0x30 else if a = 0x1000000000019 then 0x40
    else if a = 0x100000000002a then 1 else if a = 0x1000000000031 then 0x64 else 0
  rd := [⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x4000, 0⟩, ⟨0x1000000000008, 48⟩]
  wr := [⟨0x1000, 2 * pBytes + if pBytes = 128 then 20 else 32⟩, ⟨0x10000, 204800⟩]

private theorem args_of_sized (p : Nat) :
    stackArg (sizedSatState p) 0 = 0x3000 ∧ stackArg (sizedSatState p) 1 = 0 ∧
    stackArg (sizedSatState p) 2 = 0x4000 ∧ stackArg (sizedSatState p) 3 = 0 ∧
    stackArg (sizedSatState p) 4 = 0x10000 ∧ stackArg (sizedSatState p) 5 = 25600 := by
  dsimp only [stackArg, stackArgAddr, sizedSatState]
  decide +kernel

theorem sized_satisfiable (p : Nat) (hp : p = 128 ∨ p = 256 ∨ p = 384) :
    ∃ s, (Spec.Dsa.GenerationSized.contract p abi 472).pre s := by
  have hargs := args_of_sized p
  refine ⟨sizedSatState p, ?_⟩
  rcases hp with rfl | rfl | rfl
  all_goals sig_pre [Spec.Dsa.GenerationSized.contract, Spec.Dsa.generateParametersSig, abi, argRegs, stackArgs_six]
  all_goals sig_and_intros
  all_goals try simp only [hargs.1, hargs.2.1, hargs.2.2.1, hargs.2.2.2.1,
    hargs.2.2.2.2.1, hargs.2.2.2.2.2]
  all_goals first
    | exact Region.disjoint_of_sep (by decide +kernel)
    | decide +kernel
    | (intro a h₁ h₂; simp [Region.Contains, stackArgAddr, sizedSatState] at h₁ h₂ <;> bv_omega)

end VG.Proof.Dsa.X86_64.Generation.Sized
