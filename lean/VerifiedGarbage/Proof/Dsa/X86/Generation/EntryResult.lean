module
public import Aesop.BuiltinRules
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Spec.Weierstrass.Point
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Dsa.X86.Generation.EntryPlan
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Generate
import Mathlib.Tactic.Attr.Core
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometryBuffers

/-! # Move the generator's result and write footprint back to the caller's buffers -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Generation.Layout

def parameterBytes (s : State) : Option (List Byte) :=
  Spec.Dsa.generateParametersBytes (arg s 2).toNat (arg s 3).toNat
    (Spec.Rsa.bytesAt s.mem (argumentPointer s 4) (arg s 5).toNat)
    (Spec.Rsa.bytesAt s.mem (argumentPointer s 6) (arg s 7).toNat)
    (Spec.Rsa.bytesAt s.mem (argumentPointer s 8) (arg s 9).toNat)

def entryWrites (s : State) : List Region :=
  [argRegion s 10 ((arg s 11).toNat * 8), argRegion s 0 (arg s 1).toNat,
   ⟨(s.gpr .esp).setWidth 64 - 292#64, 276⟩]

def EntryResult (s initial t : State) : Prop :=
  t.gpr .eax = (if (parameterBytes s).isSome then 1 else 0) ∧
  Spec.Rsa.bytesAt t.mem (argumentPointer s 0) (arg s 1).toNat =
    (parameterBytes s).getD (List.replicate (arg s 1).toNat 0) ∧
  Frame (entryWrites s) initial.mem t.mem ∧ t.rd = initial.rd ∧ t.wr = initial.wr ∧ t.gpr .esp = initial.gpr .esp

theorem ParameterABI.writesSub {s : State} (A : ParameterABI s) (W : Nat → BitVec 32) :
    ∀ r ∈ generationWrites (A.plan W), ∃ outer ∈ entryWrites s, r.Sub outer := by
  intro r hr
  simp only [generationWrites, parameterWrites, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl | rfl | rfl) | rfl
  · exact ⟨_, List.mem_cons_self, A.arenaSub⟩
  · refine ⟨_, List.mem_cons_self, ?_⟩
    exact fun x hx => A.arenaSub x (A.geometry.part_sub (d := VG.Impl.Dsa.Generation.Layout.hash)
      (n := usedBytes A.geometry.pLen - VG.Impl.Dsa.Generation.Layout.hash)
      (by unfold usedBytes domainCheck VG.Impl.Dsa.Generation.Layout.hash; omega) x hx)
  · refine ⟨⟨(s.gpr .esp).setWidth 64 - 292#64, 276⟩, by simp [entryWrites], ?_⟩
    change Region.Sub ⟨A.geometry.frameBase, VG.Impl.Dsa.X86.Generation.frameBytes⟩ _
    rw [A.frameBase, Offset.sub_ofNat_eq _ (a := 164) (b := 292) (by decide)]
    exact Offset.sub_base _ (by decide)
  · refine ⟨⟨(s.gpr .esp).setWidth 64 - 292#64, 276⟩, by simp [entryWrites], ?_⟩
    change Region.Sub (below A.geometry.frame 128) _
    rw [A.geometry.stack_native]
    rw [A.frameBase, BitVec.sub_sub]
    change Region.Sub ⟨(s.gpr .esp).setWidth 64 - 292#64, 128⟩ _
    exact Region.sub_prefix (by decide)
  · refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
    change Region.Sub ⟨argumentPointer s 0, 2 * (arg s 2).toNat + (arg s 3).toNat⟩ _
    rw [← A.outLength]
    exact fun _ h => h

theorem generationResult_external {s initial t : State} {A : ParameterABI s} {W : Nat → BitVec 32}
    (R : GenerationResult (A.plan W) initial t) : EntryResult s initial t := by
  obtain ⟨ax, bytes, O, rd, wr, esp⟩ := R
  refine ⟨ax, ?_, O.sub (A.writesSub W), rd, wr, esp⟩
  change Spec.Rsa.bytesAt t.mem (argumentPointer s 0) (arg s 1).toNat =
    (parameterBytes s).getD (List.replicate (arg s 1).toNat 0)
  rw [A.outLength]
  exact bytes
end VG.Proof.Dsa.X86.Generation
