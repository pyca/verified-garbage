module

public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MillerRabin.Contract
public import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.Offset

/-! # A concrete prepared four-limb candidate meets the i686 round contract -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86

def satWord (k : Nat) : BitVec 64 :=
  if k = 6 then 4 else if k = 7 then 0x5555555555555555
  else if 8 ≤ k ∧ k < 16 then BitVec.ofNat 64 (0x1100 + (k - 8) * 48)
  else if k = 28 then 48 else if k = 32 then 3
  else if k = 86 then 1 else if k = 92 then 2
  else if k = 194 then 1 else if k = 198 then 2 else 0

def satArg (i : Nat) : BitVec 32 := if i = 0 then 0x1000 else 200

def satMem : Mem := fun x =>
  if (x - 0x1000).toNat < 1600 then
    (satWord ((x - 0x1000).toNat / 8)).extractLsb' (8 * ((x - 0x1000).toNat % 8)) 8
  else if (x - 0x8004).toNat < 8 then
    (satArg ((x - 0x8004).toNat / 4)).extractLsb' (8 * ((x - 0x8004).toNat % 4)) 8
  else 0

def satState : State where
  gpr r := if r = .esp then 0x8000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0x8004, 8⟩]
  wr := [⟨0x1000, 1600⟩]

theorem sat_arg0 : arg satState 0 = 0x1000#32 := by decide +kernel
theorem sat_arg1 : arg satState 1 = 200#32 := by decide +kernel

theorem sat_layout : Proof.MillerRabin.Round.Layout Proof.MillerRabin.Round.compact satMem 0x1000 200 := by
  refine ⟨Or.inr rfl, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  case refine_4 =>
    intro j hj
    have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  all_goals first
    | decide +kernel
    | change Proof.Rsa.Mont.wordAt satMem 0x1000 28 = BitVec.ofNat 64 (8 * (Proof.Rsa.Mont.wOf satMem 0x1000 + 2)); decide +kernel

theorem sat_prepared : Proof.MillerRabin.Round.Prepared Proof.MillerRabin.Round.compact satMem 0x1000 := by
  unfold Proof.MillerRabin.Round.Prepared
  decide +kernel

theorem satisfiable : ∃ s, (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96).pre s := by
  refine ⟨satState, ?_⟩
  sig_pre [Proof.MillerRabin.Round.roundContract, Proof.MillerRabin.Round.roundSig, abi, argSlots, argVal, argBytes, stackBelow]
  simp only [sat_arg0, sat_arg1]
  sig_and_intros
  all_goals first
    | exact sat_layout
    | exact sat_prepared
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)


end VG.Proof.MillerRabin.X86
