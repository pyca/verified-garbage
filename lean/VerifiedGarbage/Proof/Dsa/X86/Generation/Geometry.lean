module
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Spec.Dsa.Generate
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Frame
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Framework.X86.Exec

/-! # Concrete arena geometry shared by all 32-bit parameter-generation phases -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.Generation.Layout

structure GenerationGeometry where
  parent : BitVec 32
  frame : BitVec 32
  pLen : Nat
  qLen : Nat
  lengths : Spec.Dsa.generationLengthsValid pLen qLen
  arenaBound : parent.toNat + usedBytes pLen ≤ 2 ^ 32
  frameBound : frame.toNat + VG.Impl.Dsa.X86.Generation.frameBytes ≤ 2 ^ 32
  stackSize : 128 ≤ frame.toNat
  separated : frame.toNat + VG.Impl.Dsa.X86.Generation.frameBytes ≤ parent.toNat ∨
    parent.toNat + usedBytes pLen + 128 ≤ frame.toNat

def GenerationGeometry.base (G : GenerationGeometry) : Addr := G.parent.setWidth 64
def GenerationGeometry.frameBase (G : GenerationGeometry) : Addr := G.frame.setWidth 64
def GenerationGeometry.pointer (G : GenerationGeometry) (d : Nat) : BitVec 32 := G.parent + BitVec.ofNat 32 d
def GenerationGeometry.part (G : GenerationGeometry) (d n : Nat) : Region := ⟨off G.base d, n⟩

theorem GenerationGeometry.width (G : GenerationGeometry) : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384 := by
  rcases G.lengths with h | h | h <;> simp [h.1]

theorem GenerationGeometry.qWidth (G : GenerationGeometry) : G.qLen = 20 ∨ G.qLen = 32 := by
  rcases G.lengths with h | h | h <;> simp [h.2]

theorem GenerationGeometry.base_toNat (G : GenerationGeometry) : G.base.toNat = G.parent.toNat := by
  simp only [base, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le G.parent.isLt
    (by decide : 2 ^ 32 ≤ 2 ^ 64))]

theorem GenerationGeometry.frame_toNat (G : GenerationGeometry) : G.frameBase.toNat = G.frame.toNat := by
  simp only [frameBase, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le G.frame.isLt
    (by decide : 2 ^ 32 ≤ 2 ^ 64))]

theorem GenerationGeometry.pointer_addr (G : GenerationGeometry) {d : Nat} (hd : d < usedBytes G.pLen) :
    (G.pointer d).setWidth 64 = off G.base d := addr_eq (by have := G.arenaBound; omega)

theorem GenerationGeometry.pointer_toNat (G : GenerationGeometry) {d : Nat} (hd : d < usedBytes G.pLen) :
    (G.pointer d).toNat = G.parent.toNat + d := by
  have bound := G.arenaBound
  simp only [pointer, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : d < 2 ^ 32), Nat.mod_eq_of_lt (by omega : G.parent.toNat + d < 2 ^ 32)]

theorem GenerationGeometry.part_sub (G : GenerationGeometry) {d n : Nat} (h : d + n ≤ usedBytes G.pLen) :
    Region.Sub (G.part d n) ⟨G.base, usedBytes G.pLen⟩ := Offset.sub_base G.base h

theorem GenerationGeometry.part_bound (G : GenerationGeometry) {d n : Nat} (h : d + n ≤ usedBytes G.pLen) :
    (off G.base d).toNat + n ≤ 2 ^ 32 := by
  have bound := G.arenaBound
  have width := G.width
  have size : usedBytes G.pLen < 2 ^ 32 := by rcases width with h | h | h <;> rw [h] <;> decide
  simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat, G.base_toNat,
    Nat.mod_eq_of_lt (by omega : d < 2 ^ 64), Nat.mod_eq_of_lt (by omega : G.parent.toNat + d < 2 ^ 64)]
  omega

theorem GenerationGeometry.parts_disjoint (G : GenerationGeometry) {d n e k : Nat}
    (hd : d + n ≤ usedBytes G.pLen) (he : e + k ≤ usedBytes G.pLen)
    (apart : d + n ≤ e ∨ e + k ≤ d) : (G.part d n).Disjoint (G.part e k) := by
  have := G.arenaBound
  exact Offset.disjoint G.base apart (by omega) (by omega)

theorem GenerationGeometry.part_stk (G : GenerationGeometry) {d n : Nat}
    (hd : d < usedBytes G.pLen) (room : d + n ≤ usedBytes G.pLen) : StkOk G.frame (off G.base d) n := by
  rw [← G.pointer_addr hd]
  have ptr : ((G.pointer d).setWidth 64).toNat = (G.pointer d).toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (G.pointer d).isLt
      (by decide : 2 ^ 32 ≤ 2 ^ 64))]
  unfold StkOk
  rw [ptr, G.pointer_toNat hd]
  have := G.stackSize
  have := G.separated
  unfold VG.Impl.Dsa.X86.Generation.frameBytes at *
  exact ⟨by omega, by omega⟩
end VG.Proof.Dsa.X86.Generation
