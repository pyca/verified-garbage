module
public import Aesop.BuiltinRules
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Spec.Weierstrass.Point
import VerifiedGarbage.Proof.Dsa.X86.Generation.DrawMemory
import VerifiedGarbage.Proof.Dsa.X86.Generation.SampleMemory
public import VerifiedGarbage.Proof.Dsa.X86.Generation.CandidateTestState
import VerifiedGarbage.Proof.Dsa.X86.Generation.CandidatePreserve
import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchWrites

/-! # Controller updates preserve candidate buffers, tapes, and the prepared modulus -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Generation.Layout

theorem controlOutside_frame {G : GenerationGeometry} {s t : Mem}
    (O : Outside (off G.base VG.Impl.Dsa.Generation.Layout.control) 0 12 s t) :
    Frame [G.part VG.Impl.Dsa.Generation.Layout.control 12] s t := by
  simpa only [GenerationGeometry.part, off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using sampleOutside_frame O (by decide)

theorem control_mutable (G : GenerationGeometry) :
    ∀ r ∈ [G.part VG.Impl.Dsa.Generation.Layout.control 12], ∃ outer ∈ parameterWrites G, r.Sub outer := by
  intro r hr; obtain rfl := List.mem_singleton.mp hr
  exact ⟨_, List.mem_cons_self, G.mutablePart (by decide) (by unfold VG.Impl.Dsa.Generation.Layout.control usedBytes domainCheck; omega)⟩

theorem control_bufferApart (G : GenerationGeometry) {d n : Nat}
    (room : d + n ≤ usedBytes G.pLen) (before : d + n ≤ VG.Impl.Dsa.Generation.Layout.control) :
    ∀ r ∈ [G.part VG.Impl.Dsa.Generation.Layout.control 12], (G.part d n).Disjoint r := by
  intro r hr; obtain rfl := List.mem_singleton.mp hr
  exact G.parts_disjoint room (by unfold VG.Impl.Dsa.Generation.Layout.control usedBytes domainCheck; omega) (.inl before)

theorem control_arithmeticApart (G : GenerationGeometry) :
    ∀ r ∈ [G.part VG.Impl.Dsa.Generation.Layout.control 12], (G.part arithmetic arithmeticBytes).Disjoint r := by
  intro r hr; obtain rfl := List.mem_singleton.mp hr
  exact G.parts_disjoint (by unfold arithmetic arithmeticBytes usedBytes domainCheck; omega)
    (by unfold VG.Impl.Dsa.Generation.Layout.control usedBytes domainCheck; omega) (.inr (by decide))

theorem candidateTest_bytes {G : GenerationGeometry} {s t : Mem} {d n : Nat}
    (O : Frame (candidateTestWrites G) s t) (room : d + n ≤ usedBytes G.pLen) (before : d + n ≤ witness) :
    Spec.Rsa.bytesAt t (off G.base d) n = Spec.Rsa.bytesAt s (off G.base d) n :=
  drawFrame_bytes O (candidateTest_bufferApart G room before) (by unfold witness at before; omega)

theorem control_bytes {G : GenerationGeometry} {s t : Mem} {d n : Nat}
    (O : Outside (off G.base VG.Impl.Dsa.Generation.Layout.control) 0 12 s t)
    (room : d + n ≤ usedBytes G.pLen) (before : d + n ≤ VG.Impl.Dsa.Generation.Layout.control) :
    Spec.Rsa.bytesAt t (off G.base d) n = Spec.Rsa.bytesAt s (off G.base d) n :=
  drawFrame_bytes (controlOutside_frame O) (control_bufferApart G room before)
    (by unfold VG.Impl.Dsa.Generation.Layout.control at before; omega)
end VG.Proof.Dsa.X86.Generation
