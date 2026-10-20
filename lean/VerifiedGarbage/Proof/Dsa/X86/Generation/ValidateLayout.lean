module
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Geometry
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometryBuffers

/-! # Domain-check call arguments and its isolated 60-byte stack reservation -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Generation.Layout

def validateValue (G : GenerationGeometry) : Nat → BitVec 32
  | 0 => G.pointer packed
  | 1 => BitVec.ofNat 32 (2 * G.pLen + G.qLen)
  | 2 => BitVec.ofNat 32 G.pLen
  | 3 => BitVec.ofNat 32 G.qLen
  | 4 => G.pointer domainCheck
  | _ => BitVec.ofNat 32 (16 * G.pLen)

def validateArgsBase (G : GenerationGeometry) : Addr := (G.frame - 24#32).setWidth 64
def validateRd (G : GenerationGeometry) : List Region := [G.part packed (2 * G.pLen + G.qLen)]
def validateWr (G : GenerationGeometry) : List Region := [G.part domainCheck (128 * G.pLen), ⟨validateArgsBase G, 24⟩]
def ValidateSlots (G : GenerationGeometry) (s : State) : Prop :=
  ∀ i < 6, s.mem.readW (off (validateArgsBase G) (4 * i)) 32 = validateValue G i

theorem GenerationGeometry.stack_toNat (G : GenerationGeometry) {depth : Nat} (hd : depth ≤ 128) :
    ((G.frame - BitVec.ofNat 32 depth).setWidth 64).toNat = G.frame.toNat - depth := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _) (by decide : 2 ^ 32 ≤ 2 ^ 64)),
    sub_toNat (by have := G.stackSize; omega)]

theorem GenerationGeometry.stack_slice_sub (G : GenerationGeometry) {depth len : Nat}
    (room : len ≤ depth) (bound : depth ≤ 128) :
    (⟨(G.frame - BitVec.ofNat 32 depth).setWidth 64, len⟩ : Region).Sub (below G.frame 128) :=
  fun x hx => below_sub bound G.stackSize x (Nat.le_trans hx room)

theorem GenerationGeometry.stack_slice_apart (G : GenerationGeometry) {depth len d n : Nat}
    (room : len ≤ depth) (bound : depth ≤ 128) (arena : d + n ≤ usedBytes G.pLen) :
    (G.part d n).Disjoint ⟨(G.frame - BitVec.ofNat 32 depth).setWidth 64, len⟩ :=
  (G.stack_part_native arena (Nat.le_refl _)).symm.sub_right (G.stack_slice_sub room bound)

theorem validate_lengths (G : GenerationGeometry) : Spec.Dsa.lengthsValid G.pLen G.qLen := by
  rcases G.lengths with h | h | h <;> rw [h.1, h.2] <;> decide

theorem validate_packed_room (G : GenerationGeometry) : packed + (2 * G.pLen + G.qLen) ≤ usedBytes G.pLen := by
  have := G.width; have := G.qWidth; unfold packed usedBytes domainCheck; omega

theorem validate_scratch_room (G : GenerationGeometry) : domainCheck + 128 * G.pLen ≤ usedBytes G.pLen := by
  unfold usedBytes; omega
end VG.Proof.Dsa.X86.Generation
