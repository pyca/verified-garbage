module
import VerifiedGarbage.Proof.Mont.X86.Words
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.Exec
public import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.TCB.X86.State

/-! # Native tape pointers select exactly the complete chunks in the specification -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem tape_pointer_addr {pointer : BitVec 32} {used : Nat} (fit : pointer.toNat + used < 2 ^ 32) :
    (pointer + BitVec.ofNat 32 used).setWidth 64 = off (pointer.setWidth 64) used := addr_eq fit

theorem tape_slice {mem : Mem} {pointer : BitVec 32} {total used width : Nat}
    (fit : pointer.toNat + total ≤ 2 ^ 32) (room : used + width ≤ total) (positive : 0 < width) :
    Spec.Rsa.bytesAt mem ((pointer + BitVec.ofNat 32 used).setWidth 64) width =
      ((Spec.Rsa.bytesAt mem (pointer.setWidth 64) total).drop used).take width := by
  rw [tape_pointer_addr (by omega : pointer.toNat + used < 2 ^ 32)]
  apply List.ext_getElem
  · simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range, List.length_take, List.length_drop]
    omega
  · intro i hi hj
    simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, List.getElem_take, List.getElem_drop]
    simp only [off, BitVec.ofNat_add, BitVec.add_assoc]

theorem tape_pointer_fit {pointer : BitVec 32} {total used width : Nat}
    (fit : pointer.toNat + total ≤ 2 ^ 32) (room : used + width ≤ total) (positive : 0 < width) :
    (pointer + BitVec.ofNat 32 used).toNat + width ≤ 2 ^ 32 := by
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : used < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega : pointer.toNat + used < 2 ^ 32)]
  omega

theorem tape_slice_sub {pointer : BitVec 32} {total used width : Nat}
    (fit : pointer.toNat + total ≤ 2 ^ 32) (room : used + width ≤ total) (positive : 0 < width) :
    Region.Sub ⟨(pointer + BitVec.ofNat 32 used).setWidth 64, width⟩ ⟨pointer.setWidth 64, total⟩ := by
  rw [tape_pointer_addr (by omega : pointer.toNat + used < 2 ^ 32)]
  exact Offset.sub_base _ room

theorem tape_slice_read {s : State} {pointer : BitVec 32} {total used width : Nat}
    (fit : pointer.toNat + total ≤ 2 ^ 32) (room : used + width ≤ total) (positive : 0 < width)
    (read : ∀ d k, d + k ≤ total → InRegions (s.rd ++ s.wr) (off (pointer.setWidth 64) d) k)
    {d k : Nat} (inside : d + k ≤ width) :
    InRegions (s.rd ++ s.wr) (off ((pointer + BitVec.ofNat 32 used).setWidth 64) d) k := by
  rw [tape_pointer_addr (by omega : pointer.toNat + used < 2 ^ 32)]
  simpa only [off, BitVec.ofNat_add, BitVec.add_assoc] using read (used + d) k (by omega)
end VG.Proof.Dsa.X86.Generation
