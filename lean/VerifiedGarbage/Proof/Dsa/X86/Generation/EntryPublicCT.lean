module
public import Aesop.BuiltinRules
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import VerifiedGarbage.Spec.Weierstrass.Point
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PublicCT
public import VerifiedGarbage.Proof.Dsa.X86.Generation.EntryResources
import Mathlib.Tactic.Attr.Core

/-! # Equal disclosed inputs share an entry plan without sharing unrelated memory -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem geometry_ext {G H : GenerationGeometry} (parent : G.parent = H.parent) (frame : G.frame = H.frame)
    (p : G.pLen = H.pLen) (q : G.qLen = H.qLen) : G = H := by
  cases G; cases H; simp_all

theorem GenerationPublicAgree.geometry {s t : State} {A : ParameterABI s} {B : ParameterABI t}
    (h : GenerationPublicAgree s t) : A.geometry = B.geometry :=
  geometry_ext (h.args 10 (by decide)) (by change s.gpr .esp - 164#32 = t.gpr .esp - 164#32; rw [h.sp])
    (congrArg BitVec.toNat (h.args 2 (by decide))) (congrArg BitVec.toNat (h.args 3 (by decide)))

theorem tapeMemory_congr {G H : GenerationGeometry} {T : GenerationTape G} {U : GenerationTape H} {s : State}
    (pointer : T.pointer = U.pointer) (bytes : T.bytes = U.bytes) (R : TapeMemory T s) : TapeMemory U s := by
  constructor
  · intro d k hk
    rw [← pointer]
    exact R.read d k (by rw [bytes]; exact hk)
  · rw [← pointer, ← bytes]; exact R.value

theorem entryResources_public {s t u : State} {A : ParameterABI s} {B : ParameterABI t}
    (h : GenerationPublicAgree s t) (R : EntryResources B u) : EntryResources A u := by
  have geo : A.geometry = B.geometry := h.geometry
  refine ⟨by rw [geo]; exact R.arena, ?_, by rw [geo]; exact R.tableWrite, ?_, ?_, ?_⟩
  · refine ⟨by rw [geo]; exact R.arguments.frame, by rw [geo]; exact R.arguments.bound,
      by rw [geo]; exact R.arguments.read, ?_⟩
    intro j hj
    rw [geo, h.args j hj]
    exact R.arguments.value j hj
  · exact tapeMemory_congr (h.args 4 (by decide)).symm h.seeds.symm R.seeds
  · exact tapeMemory_congr (h.args 6 (by decide)).symm h.hs.symm R.hs
  · exact tapeMemory_congr (h.args 8 (by decide)).symm h.rand.symm R.witnesses
end VG.Proof.Dsa.X86.Generation
