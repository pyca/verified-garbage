module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.Inverse.Entry
import VerifiedGarbage.Proof.RsaKeyGen.X86.Inverse.Correct
import VerifiedGarbage.Proof.RsaKeyGen.X86.Inverse.ConstantTime
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.Contract
meta import VerifiedGarbage.Proof.RsaKeyGen.X86.Inverse.Entry
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.RsaKeyGen.Contract

/-! # `vg_rsa_keygen_inverse` is verified against its contract -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Inverse
open VG VG.X86

def satArgument : Nat → BitVec 32
  | 0 => 0x10000
  | 1 => 50
  | _ => 8

/-- A call with numbers of 8 octets: `m = 3` (numbers 1 and 8), 1, 0, `2^64 − 3` and 0, in a
workspace of 50 words at `0x10000`; the arguments above the stack pointer `0x4000`. -/
def satMemory : Mem := fun a =>
  if (a - 0x4004).toNat < 12 then
    (satArgument ((a - 0x4004).toNat / 4)).extractLsb' (8 * ((a - 0x4004).toNat % 4)) 8
  else if a = 0x100b0 then 3 else if a = 0x100c0 then 1 else if a = 0x10120 then 3 else
    if a = 0x10130 then 0xfd else if (a - 0x10131).toNat < 7 then 0xff else 0

def satState : State where
  gpr r := if r = .esp then 0x4000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMemory
  rd := [⟨0x4004, 12⟩]
  wr := [⟨0x10000, 400⟩]

theorem sat_argument0 : arg satState 0 = satArgument 0 := by decide +kernel
theorem sat_argument1 : arg satState 1 = satArgument 1 := by decide +kernel
theorem sat_argument2 : arg satState 2 = satArgument 2 := by decide +kernel

theorem satisfiable : ∃ s, contract.pre s := by
  refine ⟨satState, ?_⟩
  sig_pre [contract, inverseStack, Proof.RsaKeyGen.inverseContract, Proof.RsaKeyGen.inverseSig,
    abi, argSlots, argVal, argBytes, stackBelow]
  simp only [sat_argument0, sat_argument1, sat_argument2]
  sig_and_intros
  all_goals first
    | rfl
    | decide +kernel
    | exact Region.disjoint_of_sep (by decide +kernel)

theorem verified : Verified target VG.Impl.RsaKeyGen.X86.Inverse.code contract :=
  ⟨correct, constantTime, satisfiable⟩

end VG.Proof.RsaKeyGen.X86.Inverse
