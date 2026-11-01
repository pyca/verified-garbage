module

import VerifiedGarbage.Proof.Ffdh.X86.Cand.CTTop
public import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateABI
import Mathlib.Tactic.ToAdditive
public import VerifiedGarbage.Proof.Ffdh.X86.Cand.Top
public import VerifiedGarbage.Proof.Weierstrass.PointContract
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs

/-! # `vg_ffdh_parameter_candidate_sieved` on i686, verified -/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Cand

open VG VG.X86

def satArgument : Nat → BitVec 32
  | 0 => 0x1000
  | 1 => 64
  | 2 => 0x2000
  | 3 => 512
  | 4 => 2
  | 5 => 0x3000
  | 6 => 0
  | 7 => 0x10000
  | _ => 1056

def satMemory : Mem := fun a =>
  if (a - 0x20004).toNat < 36 then
    (satArgument ((a - 0x20004).toNat / 4)).extractLsb' (8 * ((a - 0x20004).toNat % 4)) 8
  else constMem 0x30000 VG.Impl.RsaKeyGen.TrialTable32.packed a

def satState : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMemory
  rd := [⟨0x3000, 0⟩, ⟨0x30000, 8192⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x2000, 8⟩, ⟨0x10000, 8448⟩, ⟨0x20004, 36⟩]
  syms _ := 0x30000

theorem sat_arguments (i : Nat) (index : i < 9) : arg satState i = satArgument i := by
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

private theorem single_held {m : Mem} {f : String → Addr} {name : String} {words : List (BitVec 64)}
    (H : ∀ i < words.length, m.readW (f name + BitVec.ofNat 64 (8 * i)) 64 = words.getD i 0) :
    Abi.constsHeld m f [(name, words)] := by
  intro c mem
  obtain rfl := List.mem_singleton.mp mem
  exact H

private theorem packed_regions (f : String → Addr) :
    Abi.constRegions f [(VG.Impl.RsaKeyGen.TrialTable32.symbol, VG.Impl.RsaKeyGen.TrialTable32.packed)] =
      [⟨f VG.Impl.RsaKeyGen.TrialTable32.symbol, 8192⟩] := by
  rw [Abi.constRegions_cons, Abi.constRegions_nil, VG.Proof.RsaKeyGen.X86.Candidate.packed_length]

theorem sat_table : Abi.constsHeld satState.mem (fun name => (satState.syms name).setWidth 64)
    VG.Impl.RsaKeyGen.TrialTable32.consts := by
  apply single_held
  intro i index
  have fit : 8 * VG.Impl.RsaKeyGen.TrialTable32.packed.length ≤ 2 ^ 64 := by
    rw [VG.Proof.RsaKeyGen.X86.Candidate.packed_length]; decide
  have small : i < 1024 := by simpa only [VG.Proof.RsaKeyGen.X86.Candidate.packed_length] using index
  have ix : i < VG.Impl.RsaKeyGen.TrialTable32.packed.length := by
    rw [VG.Proof.RsaKeyGen.X86.Candidate.packed_length]; exact small
  change satMemory.readW (0x30000#64 + BitVec.ofNat 64 (8 * i)) 64 = VG.Impl.RsaKeyGen.TrialTable32.packed.getD i 0
  have held := constMem_held 0x30000 VG.Impl.RsaKeyGen.TrialTable32.packed fit i ix
  refine Eq.trans (Mem.readW_congr (m := satMemory) (m' := constMem 0x30000 VG.Impl.RsaKeyGen.TrialTable32.packed) ?_) held
  intro j bound
  have address : ((0x30000#64 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j) - 0x20004#64).toNat =
      65532 + 8 * i + j := by
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  change (if _ then _ else _) = _
  apply ite_eq_right
  intro inside
  exfalso
  apply (show ¬ ((0x30000#64 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j) - 0x20004#64).toNat < 36 from by
    change ¬ ((0x30000#64 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j) - 0x20004#64).toNat < 36
    rw [address]
    omega) inside

theorem satisfiable : ∃ s, contract.pre s := by
  refine ⟨satState, ?_⟩
  sig_pre [contract, Spec.Ffdh.sievedParameterCandidateContract, Spec.Ffdh.parameterCandidateSig, abi,
    argSlots, argVal, argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts, stackBelow]
  simp only [sat_arguments 0 (by decide), sat_arguments 1 (by decide), sat_arguments 2 (by decide),
    sat_arguments 3 (by decide), sat_arguments 4 (by decide), sat_arguments 5 (by decide),
    sat_arguments 6 (by decide), sat_arguments 7 (by decide), sat_arguments 8 (by decide)]
  simp only [packed_regions, List.forall_mem_singleton]
  sig_and_intros
  all_goals first
    | exact sat_table
    | rfl
    | decide +kernel
    | exact Region.disjoint_of_sep (by decide +kernel)
    | (unfold Spec.Rsa.scratchWords; decide +kernel)

theorem verified : Verified target Impl.Ffdh.X86.Candidate.code contract :=
  ⟨correct, constantTime, satisfiable⟩

end VG.Proof.Ffdh.X86.Cand
