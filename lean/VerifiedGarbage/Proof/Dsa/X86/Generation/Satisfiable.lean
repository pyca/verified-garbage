module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.ABI
public import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.ABIEntry
import VerifiedGarbage.Proof.Framework.Sig

/-! # A state meets the precondition: 1024-bit p, 160-bit q, an empty tape

`state` at `0x12000` holds `[0, 128, 32769 · 128, 0]`. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86

def satArgument : Nat → BitVec 32
  | 0 => 0x10000
  | 1 => 276
  | 2 => 0x11000
  | 3 => 0x20000
  | 4 => 0
  | 5 => 0x100000
  | 6 => 9216
  | _ => 0x12000

/-- The arguments at the stack pointer plus 4. -/
def satArguments : Mem := fun a =>
  (satArgument ((a - 0x80004#64).toNat / 4)).extractLsb' (8 * ((a - 0x80004#64).toNat % 4)) 8

def satMemory : Mem := fun a =>
  if (a - 0x80004#64).toNat < 32 then satArguments a
  else if a.toNat = 0x12008 then 0x80
  else if a.toNat = 0x12010 then 0x80
  else if a.toNat = 0x12012 then 0x40
  else constMem 0x30000#64 VG.Impl.RsaKeyGen.TrialTable32.packed a

def satState : State where
  gpr r := if r = .esp then 0x80000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMemory
  rd := [⟨0x20000, 0⟩, ⟨0x30000, 8192⟩]
  wr := [⟨0x10000, 276⟩, ⟨0x11000, 8⟩, ⟨0x100000, 73728⟩, ⟨0x12000, 32⟩, ⟨0x80004, 32⟩]
  syms _ := 0x30000

theorem sat_argument_word (i : Nat) (index : i < 8) :
    satArguments.readW (BitVec.ofNat 64 (0x80004 + 4 * i)) 32 = satArgument i := by
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem sat_arguments (i : Nat) (index : i < 8) : arg satState i = satArgument i := by
  have address : argAddr satState i = BitVec.ofNat 64 (0x80004 + 4 * i) := by
    change ((0x80000#32 + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64) = _
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  unfold arg
  rw [address, ← sat_argument_word i index]
  apply Mem.readW_congr
  intro j hj
  change (if _ then _ else _) = _
  refine ite_eq_left ?_
  change ((BitVec.ofNat 64 (0x80004 + 4 * i) + BitVec.ofNat 64 j) - 0x80004#64).toNat < 32
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

private theorem single_held {m : Mem} {f : String → Addr} {name : String} {words : List (BitVec 64)}
    (H : ∀ i < words.length, m.readW (f name + BitVec.ofNat 64 (8 * i)) 64 = words.getD i 0) :
    Abi.constsHeld m f [(name, words)] := by
  intro c mem
  obtain rfl := List.mem_singleton.mp mem
  exact H

private theorem packed_regions (f : String → Addr) :
    Abi.constRegions f [(VG.Impl.RsaKeyGen.TrialTable32.symbol, VG.Impl.RsaKeyGen.TrialTable32.packed)] =
      [⟨f VG.Impl.RsaKeyGen.TrialTable32.symbol, 8192⟩] := by
  rw [Abi.constRegions_cons, Abi.constRegions_nil, VG.Proof.Dsa.X86.ProbablePrime.packed_length]

theorem sat_table :
    Abi.constsHeld satState.mem (fun name => (satState.syms name).setWidth 64)
      VG.Impl.RsaKeyGen.TrialTable32.consts := by
  apply single_held
  intro i index
  have fit : 8 * VG.Impl.RsaKeyGen.TrialTable32.packed.length ≤ 2 ^ 64 := by
    rw [VG.Proof.Dsa.X86.ProbablePrime.packed_length]; decide
  have small : i < 1024 := by simpa only [VG.Proof.Dsa.X86.ProbablePrime.packed_length] using index
  change satMemory.readW (0x30000#64 + BitVec.ofNat 64 (8 * i)) 64 =
    VG.Impl.RsaKeyGen.TrialTable32.packed.getD i 0
  have held := constMem_held 0x30000 VG.Impl.RsaKeyGen.TrialTable32.packed fit i index
  refine Eq.trans (Mem.readW_congr (m := satMemory)
    (m' := constMem 0x30000 VG.Impl.RsaKeyGen.TrialTable32.packed) ?_) held
  intro j hj
  have e : (0x30000#64 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j).toNat = 0x30000 + 8 * i + j := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  change (if _ then _ else if _ then _ else if _ then _ else if _ then _ else _) = _
  rw [ite_eq_right (by simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]; omega),
    ite_eq_right (by rw [e]; omega), ite_eq_right (by rw [e]; omega), ite_eq_right (by rw [e]; omega)]
  rfl

theorem sat_w0 : satMemory.readW (BitVec.setWidth 64 (satArgument 7)) 64 = 0#64 := by decide +kernel

theorem sat_w8 : satMemory.readW (BitVec.setWidth 64 (satArgument 7) + 8) 64 = 128#64 := by decide +kernel

theorem sat_w16 : satMemory.readW (BitVec.setWidth 64 (satArgument 7) + 16) 64 = BitVec.ofNat 64 (32769 * 128) := by
  decide +kernel

theorem sat_argAddr : argAddr satState 0 = 0x80004#64 := by
  change ((0x80000#32 + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64) = _
  decide

theorem satisfiable : ∃ s, genContract.pre s := by
  refine ⟨satState, ?_⟩
  sig_pre [genContract, Spec.Dsa.parameterSearchContract, Spec.Dsa.parameterSearchSig,
    abi, argSlots, argVal, argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts, stackBelow]
  simp only [sat_arguments 0 (by decide), sat_arguments 1 (by decide), sat_arguments 2 (by decide),
    sat_arguments 3 (by decide), sat_arguments 4 (by decide), sat_arguments 5 (by decide),
    sat_arguments 6 (by decide), sat_arguments 7 (by decide), sat_argAddr]
  simp only [packed_regions, List.forall_mem_singleton]
  simp only [sat_w0, sat_w8, sat_w16]
  sig_and_intros
  all_goals first
    | exact sat_table
    | rfl
    | decide +kernel
    | exact Region.disjoint_of_sep (by decide +kernel)

end VG.Proof.Dsa.X86.Generation
