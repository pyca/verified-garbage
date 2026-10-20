module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometryTape
public import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Dsa.X86.Generation.DrawMemory
public import VerifiedGarbage.Proof.Dsa.X86.Generation.TapeSlice -- shake: keep (proof fields of exposed definitions)

/-! # Immutable tape contents and complete slices share the caller's read permissions -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

structure TapeMemory {G : GenerationGeometry} (T : GenerationTape G) (s : State) : Prop where
  read : ∀ d k, d + k ≤ T.bytes.length → InRegions (s.rd ++ s.wr) (off (T.pointer.setWidth 64) d) k
  value : Spec.Rsa.bytesAt s.mem (T.pointer.setWidth 64) T.bytes.length = T.bytes

theorem TapeMemory.keep {G : GenerationGeometry} {T : GenerationTape G} {s t : State} {rs : List Region} {regs : List Reg}
    (R : TapeMemory T s) (O : Frame rs s.mem t.mem)
    (apart : ∀ r ∈ rs, (⟨T.pointer.setWidth 64, T.bytes.length⟩ : Region).Disjoint r)
    (K : Keeps regs s t) : TapeMemory T t :=
  ⟨by intro d k hk; rw [K.2.1, K.2.2]; exact R.read d k hk,
    (drawFrame_bytes O apart (by have := T.size; omega)).trans R.value⟩

theorem TapeMemory.byte {G : GenerationGeometry} {T : GenerationTape G} {s : State}
    (R : TapeMemory T s) {i : Nat} (hi : i < T.bytes.length) :
    s.mem (off (T.pointer.setWidth 64) i) = T.bytes.getD i 0 := by
  have value := congrArg (fun bs : List Byte => bs.getD i 0) R.value
  simpa [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, hi] using value

def GenerationTape.slice {G : GenerationGeometry} (T : GenerationTape G) (used width : Nat)
    (room : used + width ≤ T.bytes.length) (positive : 0 < width) : GenerationTape G := by
  have length : ((T.bytes.drop used).take width).length = width := by
    simp only [List.length_take, List.length_drop]; omega
  have sub := tape_slice_sub T.fit room positive
  refine ⟨T.pointer + BitVec.ofNat 32 used, (T.bytes.drop used).take width,
    by rw [length]; have := T.size; omega, by rw [length]; exact tape_pointer_fit T.fit room positive, ?_, ?_, ?_⟩
  · rw [length]; exact T.arena.sub_left sub
  · rw [length]; exact T.frame.sub_left sub
  · rw [length]; exact T.stack.sub_left sub

theorem TapeMemory.slice {G : GenerationGeometry} {T : GenerationTape G} {s : State}
    (R : TapeMemory T s) (used width : Nat) (room : used + width ≤ T.bytes.length) (positive : 0 < width) :
    TapeMemory (T.slice used width room positive) s := by
  have length : ((T.bytes.drop used).take width).length = width := by
    simp only [List.length_take, List.length_drop]; omega
  refine ⟨?_, ?_⟩
  · intro d k hk
    change d + k ≤ ((T.bytes.drop used).take width).length at hk
    rw [length] at hk
    exact tape_slice_read T.fit room positive R.read hk
  · change Spec.Rsa.bytesAt s.mem ((T.pointer + BitVec.ofNat 32 used).setWidth 64)
      ((T.bytes.drop used).take width).length = (T.bytes.drop used).take width
    rw [length, tape_slice T.fit room positive, R.value]
end VG.Proof.Dsa.X86.Generation
