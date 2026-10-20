module
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometryPrime
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeFrameInputs
import VerifiedGarbage.Proof.Dsa.BitLengthBounds
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ArenaReady
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometryBuffers
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometrySeparate

/-! # Concrete search-frame resources for testing q or a full-width p candidate -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Generation.Layout

theorem generationPrimeInputs {G : GenerationGeometry} {T : GenerationTape G}
    {s : State} {W : Nat → BitVec 32} {len m used offset : Nat}
    (R : ArenaReady G s) (slots : FrameWords s.mem G.frameBase W)
    (parent : W 5 = G.parent) (candidate : W 22 = G.pointer offset)
    (lo : 4 ≤ len) (hi : len ≤ 384) (words : len % 4 = 0)
    (bits : Spec.RsaKeyGen.bitLength m = 8 * len) (odd : m % 2 = 1)
    (room : offset + len ≤ usedBytes G.pLen) (before : offset + len ≤ arithmetic)
    (value : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (off G.base offset) len) = m)
    (tape : W 13 = T.pointer) (tapeLen : W 15 = BitVec.ofNat 32 T.bytes.length)
    (usedValue : W 16 = BitVec.ofNat 32 used) (usedBound : used ≤ T.bytes.length)
    (tapeRead : ∀ i < T.bytes.length, InRegions (s.rd ++ s.wr) (off (T.pointer.setWidth 64) i) 1) :
    PrimeFrameInputs (G.prime T len m lo hi words bits odd) G.frameBase W used s := by
  have ar : arithmetic + arithmeticBytes ≤ usedBytes G.pLen := by unfold arithmetic arithmeticBytes usedBytes domainCheck; omega
  have ast : arithmetic < usedBytes G.pLen := by unfold arithmeticBytes at ar; omega
  have wr : witness + len ≤ usedBytes G.pLen := by unfold witness usedBytes domainCheck; omega
  have wst : witness < usedBytes G.pLen := by omega
  have st : offset < usedBytes G.pLen := by omega
  have gtOne : 1 < m := by
    have bounds := (VG.Proof.Dsa.bitLength_iff_bounds (by omega : 0 < 8 * len)).mp bits
    have small := Nat.pow_le_pow_right (n := 2) (by decide) (by omega : 2 ≤ 8 * len - 1)
    have four : (2 : Nat) ^ 2 = 4 := by decide
    rw [four] at small
    omega
  refine ⟨R.frame, slots, ?_, R.arithmeticWrite, G.part_bound ar, ?_, G.frame_part ar, ?_, ?_, ?_, ?_, ?_, odd, gtOne,
    tape, tapeLen, usedValue, usedBound, ?_, tapeRead, ?_, ?_, ?_⟩
  · change (W 5 + BitVec.ofNat 32 arithmetic).setWidth 64 = off G.base arithmetic
    rw [parent]
    exact G.pointer_addr ast
  · change StkOk (s.gpr .esp) (off G.base arithmetic) arithmeticBytes
    rw [R.frameReg]
    exact G.part_stk ast ar
  · change (⟨G.frameBase, VG.Impl.Dsa.X86.Generation.frameBytes⟩ : Region).Disjoint ⟨(G.pointer witness).setWidth 64, len⟩
    rw [G.pointer_addr wst]
    exact G.frame_part wr
  · change (W 22).toNat + len ≤ 2 ^ 32
    rw [candidate]
    exact G.pointer_fit st room
  · intro d hd
    change InRegions (s.rd ++ s.wr) (off ((W 22).setWidth 64) d) 4
    rw [candidate]
    exact R.readPointer st room d 4 hd
  · change (⟨(W 22).setWidth 64, len⟩ : Region).Disjoint ⟨off G.base arithmetic, arithmeticBytes⟩
    rw [candidate, G.pointer_addr st]
    exact G.parts_disjoint room ar (.inl before)
  · change Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((W 22).setWidth 64) len) = m
    rw [candidate, G.pointer_addr st]
    exact value
  · change W 5 + BitVec.ofNat 32 witness = G.pointer witness
    rw [parent]
    rfl
  · intro d hd
    exact R.readPointer wst wr d 4 hd
  · intro i hi
    change i < len at hi
    exact R.readPointer wst wr i 1 (by omega)
  · intro i hi
    change i < len at hi
    exact R.writePointer wst wr i 1 (by omega)
end VG.Proof.Dsa.X86.Generation
