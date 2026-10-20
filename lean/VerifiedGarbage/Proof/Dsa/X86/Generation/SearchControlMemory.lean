module
public import Aesop.BuiltinRules
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Spec.Weierstrass.Point
import VerifiedGarbage.Proof.Dsa.X86.Generation.SampleMemory
import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameMemory
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchContext
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometrySeparate
import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchWrites

/-! # Counter values survive phases that temporarily use EDI for arithmetic -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Generation.Layout

structure ControlValues (G : GenerationGeometry) (counter stride : Nat) (mem : Mem) : Prop where
  count : mem.readW (off (off G.base VG.Impl.Dsa.Generation.Layout.control) 0) 32 = BitVec.ofNat 32 counter
  offset : mem.readW (off (off G.base VG.Impl.Dsa.Generation.Layout.control) 4) 32 = BitVec.ofNat 32 (1 + counter * stride)

theorem ControlValues.frame {G : GenerationGeometry} {counter stride : Nat} {s t : Mem} {rs : List Region}
    (C : ControlValues G counter stride s) (O : Frame rs s t)
    (apart : ∀ r ∈ rs, (G.part VG.Impl.Dsa.Generation.Layout.control 8).Disjoint r) : ControlValues G counter stride t := by
  have word (d : Nat) (hd : d + 4 ≤ 8) :
      t.readW (off (off G.base VG.Impl.Dsa.Generation.Layout.control) d) 32 = s.readW (off (off G.base VG.Impl.Dsa.Generation.Layout.control) d) 32 :=
    O.readW (r := G.part VG.Impl.Dsa.Generation.Layout.control 8) (Offset.contains_base _ hd (by omega)) apart (by decide)
  exact ⟨(word 0 (by decide)).trans C.count, (word 4 (by decide)).trans C.offset⟩

theorem SearchContext.control {P : SearchContextPlan} {W : Nat → BitVec 32} {s t : State} {regs : List Reg}
    (R : SearchContext P W s) (O : Outside (off P.geometry.base VG.Impl.Dsa.Generation.Layout.control) 0 12 s.mem t.mem)
    (K : Keeps regs s t) (sp : .esp ∉ regs) : SearchContext P W t := by
  have room : VG.Impl.Dsa.Generation.Layout.control + 12 ≤ usedBytes P.geometry.pLen := by unfold VG.Impl.Dsa.Generation.Layout.control usedBytes domainCheck; omega
  have F : Frame [P.geometry.part VG.Impl.Dsa.Generation.Layout.control 12] s.mem t.mem := by
    simpa only [GenerationGeometry.part, off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using sampleOutside_frame O (by decide)
  exact R.frame (R.representation.keep F (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact P.geometry.frame_part room))
    (fun _ _ _ => rfl) (F.sub (by
      intro r hr; obtain rfl := List.mem_singleton.mp hr
      exact ⟨_, List.mem_cons_self, P.geometry.mutablePart (by decide) room⟩)) K sp
end VG.Proof.Dsa.X86.Generation
