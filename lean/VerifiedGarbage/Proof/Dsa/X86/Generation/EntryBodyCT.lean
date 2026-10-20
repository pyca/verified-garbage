module
public meta import VerifiedGarbage.Impl.Dsa.X86.Generation.Entry
public meta import VerifiedGarbage.Proof.Framework.X86.RelCT
public import Aesop.BuiltinRules
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import VerifiedGarbage.Spec.Weierstrass.Point
public import VerifiedGarbage.Proof.Dsa.X86.Generation.EntryResources
public import VerifiedGarbage.Proof.Dsa.X86.Generation.DispatchCTState
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Hashes
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CheckCall
import VerifiedGarbage.Proof.Dsa.X86.Generation.DispatchCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameCT

/-! # Entry setup publishes only the live argument slots used by the search -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

def EntryPublic := {s : State // ParameterABI s}
def EntryPublic.plan (p : EntryPublic) : SearchContextPlan := p.property.plan (fun _ => 0)

theorem initialWords_live (args V W : Nat → BitVec 32) {i : Nat} (bound : i < 37)
    (fixed : i ∉ parameterMutableSlots) : initialWords args V i = initialWords args W i := by
  have cases : i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 11 ∨
      i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 17 ∨ i = 18 := by
    simp only [parameterMutableSlots, List.mem_cons, List.not_mem_nil, or_false] at fixed
    omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem entryReady_ct : RelCT isa (Two fun p : EntryPublic => EntryResources p.property)
    (.block (entryIncoming ++ entryDerived)) (Two fun (p : EntryPublic) => DispatchBefore p.plan) := by
  refine two_piece [.esp] ?_ (by taint_decide) ?_
  · intro p s t hs ht r hr
    obtain rfl := List.mem_singleton.mp hr
    exact hs.arena.frameReg.trans ht.arena.frameReg.symm
  · intro p s R
    refine WP.mono (entryStorage_ok R (observedWords_rep p.property.geometry.frameBase s)) fun t ⟨Rt, _, _⟩ => ?_
    refine ⟨_, ⟨Rt.arena, Rt.representation, ?_, Rt.tableWrite, Rt.seeds, Rt.hs, Rt.witnesses⟩, rfl⟩
    intro i hi hx
    exact (Rt.fixed i hi hx).trans (initialWords_live _ _ _ hi hx)

theorem entryBody_ct (H : GenerationHashes) (F : KeyRandom.CheckCall.CheckFn) :
    RelCT isa (Two fun p : EntryPublic => EntryResources p.property)
      (entryBody H.sha1 H.sha256 F.name F.code) (fun _ _ => True) :=
  RelCT.seq entryReady_ct (two_map EntryPublic.plan (fun _ _ h => h) (dispatch_ct H F))
end VG.Proof.Dsa.X86.Generation
