module
public import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Dsa.Generate
public import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.Contract

/-! # A concrete valid empty-tape call witnesses the generation precondition -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86

def satState : State where
  gpr r := if r = .esp then 0x40000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x40005 then 16 else if a = 0x40008 then 20 else if a = 0x40009 then 1 else if a = 0x4000c then 128 else if a = 0x40010 then 20 else if a = 0x40015 then 48 else if a = 0x4001d then 64 else if a = 0x40025 then 80 else if a = 0x4002e then 1 else if a = 0x40031 then 36 else 0
  rd := [⟨0x3000, 0⟩, ⟨0x4000, 0⟩, ⟨0x5000, 0⟩]
  wr := [⟨0x1000, 276⟩, ⟨0x10000, 73728⟩, ⟨0x40004, 48⟩]

theorem generation_satisfiable : ∃ s, (Spec.Dsa.generateParametersContract abi 292).pre s := by
  have a0 : arg satState 0 = 4096 := by decide
  have a1 : arg satState 1 = 276 := by decide
  have a2 : arg satState 2 = 128 := by decide
  have a3 : arg satState 3 = 20 := by decide
  have a4 : arg satState 4 = 12288 := by decide
  have a5 : arg satState 5 = 0 := by decide
  have a6 : arg satState 6 = 16384 := by decide
  have a7 : arg satState 7 = 0 := by decide
  have a8 : arg satState 8 = 20480 := by decide
  have a9 : arg satState 9 = 0 := by decide
  have a10 : arg satState 10 = 65536 := by decide
  have a11 : arg satState 11 = 9216 := by decide
  have e : argAddr satState 0 = 0x40004 := by decide
  have esp : satState.gpr .esp = 0x40000 := rfl
  sig_implies_sat [Spec.Dsa.generateParametersContract, Spec.Dsa.generateParametersSig, abi, argSlots, argVal, argBytes,
    stackBelow] [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, e, esp, satState] using satState
end VG.Proof.Dsa.X86.Generation
