module

public import VerifiedGarbage.Proof.MillerRabin.X86.ABI
import VerifiedGarbage.Proof.MillerRabin.X86.WorkspaceCongruence
import VerifiedGarbage.Proof.MillerRabin.Example
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Offset

/-! # A valid cdecl input reuses the shared four-limb candidate-three workspace -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont

private def satMem : Mem := fun x =>
  if 0x8004 ≤ x.toNat ∧ x.toNat < 0x800c then
    (0x0000010000001000 : BitVec 64).extractLsb' (8 * (x.toNat - 0x8004)) 8
  else VG.Proof.MillerRabin.Example.satMem x

private def satState : State where
  gpr r := if r = .esp then 0x8000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0x8004, 8⟩]
  wr := [⟨0x1000, 2048⟩]

private theorem sat_same (i : Nat) (hi : i < 8 * 256) :
    satMem (off 0x1000 i) = VG.Proof.MillerRabin.Example.satMem (off 0x1000 i) := by
  have small : (off 0x1000 i).toNat < 0x8004 := by
    simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]
    change (4096 + i % 2 ^ 64) % 2 ^ 64 < 32772
    omega
  simp only [satMem, ite_eq_right (show ¬(0x8004 ≤ (off 0x1000 i).toNat ∧ (off 0x1000 i).toNat < 0x800c) by omega)]

theorem round_satisfiable : ∃ s, (Spec.MillerRabin.roundContract abi Spec.MillerRabin.compact stackBytes).pre s := by
  have valid := workspace_congr sat_same VG.Proof.MillerRabin.Example.sat_layout VG.Proof.MillerRabin.Example.sat_prepared
  have a0 : arg satState 0 = 0x1000 := by decide +kernel
  have a1 : arg satState 1 = 256 := by decide +kernel
  refine ⟨satState, ?_⟩
  sig_pre [Spec.MillerRabin.roundContract, Spec.MillerRabin.roundSig, abi, argSlots, argVal, argBytes,
    stackBelow]
  simp only [a0, a1]
  sig_and_intros
  all_goals first
    | exact valid.1
    | exact valid.2.1
    | exact Region.disjoint_of_le (by decide +kernel) (by decide +kernel) (by decide +kernel)
    | decide +kernel

end VG.Proof.MillerRabin.X86
