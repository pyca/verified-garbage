module

public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Top
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Callee
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.X86.PublicSave
public import VerifiedGarbage.Proof.Rsa.Contract

/-! # The cdecl frame of public RSA at a run-time width

The callee-saved registers the entry saves in the working space
(`frame_saved`, `frame_full`), and the return address above the 96 bytes of
stack below `esp` that the calls use (`ret_below`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.PublicRt

open VG VG.X86 VG.X86.Spill VG.Impl.Bignum.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Proof.Bignum.X86.PublicContext
open VG.Proof.Dsa.X86 (argumentPointer)

theorem frame_saved {base out : Addr} {bytes len : Nat} {sp : BitVec 32} {m m' : Mem} {g : Reg → BitVec 32}
    (F : Frame [⟨off base 16, bytes - 16⟩, ⟨out, len⟩, below sp 96] m m')
    (A : Region.Disjoint ⟨base, bytes⟩ ⟨out, len⟩) (low : 16 ≤ bytes) (high : bytes ≤ 2 ^ 64)
    (Z : Region.Disjoint (below sp 96) ⟨base, bytes⟩)
    (S : Saved m (off base) g PublicFn.savedRegisters) : Saved m' (off base) g PublicFn.savedRegisters := by
  intro p hp
  have B : p.2 + 4 ≤ 16 := by
    simp only [PublicFn.savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> decide
  refine (F.readW (r := ⟨base, 16⟩) (Offset.contains_base _ B (by omega)) ?_ (by decide)).trans (S p hp)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Offset.base_disjoint base (Nat.le_refl 16) (by omega)
  · exact A.sub_left (Region.sub_prefix (by omega))
  · exact (Z.sub_right (Region.sub_prefix (by omega))).symm

theorem frame_full {base out : Addr} {bytes len : Nat} {sp : BitVec 32} {m m' : Mem}
    (F : Frame [⟨off base 16, bytes - 16⟩, ⟨out, len⟩, below sp 96] m m') (low : 16 ≤ bytes) :
    Frame [⟨base, bytes⟩, ⟨out, len⟩, below sp 96] m m' := by
  apply F.sub
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨⟨base, bytes⟩, by simp, Offset.sub_base base (by omega)⟩
  · exact ⟨⟨out, len⟩, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

/-- The return address lies above the stack the calls use. -/
theorem ret_below {sp : BitVec 32} (h : 96 ≤ sp.toNat) :
    Region.Disjoint ⟨sp.setWidth 64, 4⟩ (below sp 96) := by
  simp only [below]
  rw [VG.X86.Taint.sub_setWidth h]
  exact Offset.base_disjoint_below _ (by decide)

end VG.Proof.Bignum.X86.PublicRt
