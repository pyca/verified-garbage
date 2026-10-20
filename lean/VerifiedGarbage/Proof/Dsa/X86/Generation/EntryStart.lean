module
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Dsa.X86.Generation.EntryGeometry
public import VerifiedGarbage.Proof.Dsa.X86.Generation.TapeMemory
public import VerifiedGarbage.Proof.Framework.X86.Inline
import VerifiedGarbage.Proof.Dsa.X86.Generation.DrawMemory

/-! # Resources at the inner entry, before narrowing scratch permissions -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Generation.Layout

structure EntryStart {s : State} (A : ParameterABI s) (t : State) : Prop where
  esp : t.gpr .esp = A.geometry.frame
  rd : t.rd = s.rd
  frameWrite : (⟨A.geometry.frameBase, VG.Impl.Dsa.X86.Generation.frameBytes⟩ : Region) ∈ t.wr
  scratchWrite : argRegion s 10 ((arg s 11).toNat * 8) ∈ t.wr
  outWrite : argRegion s 0 (arg s 1).toNat ∈ t.wr
  argsWrite : (⟨argAddr s 0, 48⟩ : Region) ∈ t.wr
  memory : Frame [⟨(s.gpr .esp).setWidth 64 - 292#64, 292⟩] s.mem t.mem

def bodyWrites {s : State} (A : ParameterABI s) : List Region :=
  [⟨A.geometry.frameBase, VG.Impl.Dsa.X86.Generation.frameBytes⟩,
   ⟨A.geometry.base, usedBytes A.geometry.pLen⟩,
   A.geometry.part arithmetic arithmeticBytes,
   A.geometry.part VG.Impl.Dsa.Generation.Layout.control 12,
   ⟨A.geometry.base, 8192⟩,
   argRegion s 0 (arg s 1).toNat,
   ⟨argAddr s 0, 48⟩]

theorem entryTapeMemory {s t : State} {A : ParameterABI s} {T : GenerationTape A.geometry}
    (start : EntryStart A t) (member : (⟨T.pointer.setWidth 64, T.bytes.length⟩ : Region) ∈ s.rd)
    (bytes : T.bytes = Spec.Rsa.bytesAt s.mem (T.pointer.setWidth 64) T.bytes.length)
    (apart : (⟨T.pointer.setWidth 64, T.bytes.length⟩ : Region).Disjoint
      ⟨(s.gpr .esp).setWidth 64 - 292#64, 292⟩) :
    TapeMemory T (t.withRegions s.rd (bodyWrites A)) := by
  refine ⟨?_, ?_⟩
  · intro d k hk
    exact ⟨_, List.mem_append_left _ member, Offset.contains_base _ hk (by have := T.size; omega)⟩
  · exact (drawFrame_bytes start.memory (by
      intro r hr; obtain rfl := List.mem_singleton.mp hr; exact apart) (by have := T.size; omega)).trans bytes.symm
end VG.Proof.Dsa.X86.Generation
