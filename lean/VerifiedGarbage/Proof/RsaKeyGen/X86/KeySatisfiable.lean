module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyABI
import VerifiedGarbage.Proof.Framework.Contract
import Mathlib.Tactic.IntervalCases

/-! # A disjoint native caller satisfies the complete key-generation precondition -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86

def satArgument : Nat → BitVec 32
  | 0 => 0x1000
  | 1 => 64
  | 2 => 0x2000
  | 3 => 64
  | 4 => 0x3000
  | 5 => 32
  | 6 => 0x4000
  | 7 => 32
  | 8 => 0x5000
  | 9 => 32
  | 10 => 0x6000
  | 11 => 32
  | 12 => 0x7000
  | 13 => 32
  | 14 => 0x8000
  | 15 => 1
  | 16 => 0x10000
  | _ => 1056

def satMemory : Mem := fun a =>
  if (a - 0x20004).toNat < 72 then
    (satArgument ((a - 0x20004).toNat / 4)).extractLsb' (8 * ((a - 0x20004).toNat % 4)) 8
  else 0

def satState : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMemory
  rd := [⟨0x8000, 1⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x2000, 64⟩, ⟨0x3000, 32⟩, ⟨0x4000, 32⟩,
    ⟨0x5000, 32⟩, ⟨0x6000, 32⟩, ⟨0x7000, 32⟩, ⟨0x10000, 8448⟩, ⟨0x20004, 72⟩]

theorem sat_arguments (i : Nat) (hi : i < 18) : arg satState i = satArgument i := by
  interval_cases i <;> decide +kernel

theorem satisfiable : ∃ s, contract.pre s := by
  refine ⟨satState, ?_⟩
  sig_pre [contract, keyStack, Spec.RsaKeyGen.keyContract, Spec.RsaKeyGen.keySig,
    abi, argSlots, argVal, argBytes, stackBelow]
  simp only [sat_arguments 0 (by decide), sat_arguments 1 (by decide), sat_arguments 2 (by decide),
    sat_arguments 3 (by decide), sat_arguments 4 (by decide), sat_arguments 5 (by decide),
    sat_arguments 6 (by decide), sat_arguments 7 (by decide), sat_arguments 8 (by decide),
    sat_arguments 9 (by decide), sat_arguments 10 (by decide), sat_arguments 11 (by decide),
    sat_arguments 12 (by decide), sat_arguments 13 (by decide), sat_arguments 14 (by decide),
    sat_arguments 15 (by decide), sat_arguments 16 (by decide), sat_arguments 17 (by decide)]
  sig_and_intros
  all_goals first
    | rfl
    | decide +kernel
    | exact Region.disjoint_of_sep (by decide +kernel)
    | (unfold Spec.RsaKeyGen.primeLenValid; decide +kernel)
    | (unfold Spec.Rsa.scratchWords; decide +kernel)

end VG.Proof.RsaKeyGen.X86.Key
