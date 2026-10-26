module

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCallArgs
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCallValid
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyGeometry
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Mont.X86.Compact.Frame
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCallGeometry
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.Prop
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.ToAdditive

/-! # Native key writes preserve the saved cdecl registers and return address -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem call_writes {s : State} (h : contract.pre s) :
    (callEnvironment s).outputs.writes = callWorkspace s :: callOutputs s := by
  have v := call_valid h
  have Z := call_sizes h
  change callWorkspace s :: (List.range 7).map (callEnvironment s).outputs.region =
    callWorkspace s :: (List.range 7).map (callOutput s)
  congr 1
  apply List.map_congr_left
  intro i hi
  have bound := List.mem_range.mp hi
  rw [v.outputRegion bound, Z.outputRegion bound]

theorem writes_reserved {s : State} (h : contract.pre s) :
    ∀ r ∈ (callEnvironment s).outputs.writes, r.Disjoint (reservedRegion s) := by
  have D := call_separation h
  rw [call_writes h]
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact D.stackWorkspace
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
    exact D.stackOutput i (List.mem_range.mp hi)

theorem writes_return {s : State} (h : contract.pre s) :
    ∀ r ∈ (callEnvironment s).outputs.writes, (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint r := by
  have D := call_separation h
  rw [call_writes h]
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact D.returnWorkspace
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
    exact D.returnOutput i (List.mem_range.mp hi)

theorem saved_read {s t : State} (h : contract.pre s)
    (F : Frame (callEnvironment s).outputs.writes (Compact.entered s).mem t.mem) {i : Nat} (hi : i < 4) :
    t.mem.readW (addr (callSp s) (4 * i)) 32 =
      s.gpr (Compact.savedRegisters[3 - i]'(by change 3 - i < 4; omega)) := by
  have A := call_layout h
  have fit : 16 ≤ (s.gpr .esp).toNat := by have := A.low; omega
  have pFit : (callSp s).toNat + 16 ≤ 2 ^ 32 := by
    rw [A.privateNat]
    have := (s.gpr .esp).isLt
    omega
  have same := F.readW (r := (⟨(callSp s).setWidth 64, 16⟩ : Region))
    (a := addr (callSp s) (4 * i)) (w := 32)
    (by rw [addr_eq (by omega)]; exact Offset.contains_base _ (by omega) (by omega))
    (fun r hr => ((writes_reserved h r hr).sub_right A.savedSub).symm) (by decide)
  have word := pushed_word (rs := Compact.savedRegisters) (s := s) (by decide) fit hi
  change (Compact.entered s).mem.readW (addr ((Compact.entered s).gpr .esp) (4 * i)) 32 = _ at word
  rw [Compact.entered, pushed_esp] at word
  exact same.trans word

theorem return_read {s t : State} (h : contract.pre s)
    (F : Frame (callEnvironment s).outputs.writes (Compact.entered s).mem t.mem) :
    t.mem.readW ((s.gpr .esp).setWidth 64) 32 = s.mem.readW ((s.gpr .esp).setWidth 64) 32 := by
  have A := call_layout h
  have fit : 16 ≤ (s.gpr .esp).toNat := by have := A.low; omega
  have same := F.readW (w := 32) (Region.contains_self ((s.gpr .esp).setWidth 64) 4)
    (writes_return h) (by decide)
  have pushed := pushed_frame (rs := Compact.savedRegisters) (s := s) (by decide) fit
  have separate : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (below (s.gpr .esp) 16) := by
    unfold below
    rw [Taint.sub_setWidth fit]
    exact Offset.base_disjoint_below _ (by decide)
  exact same.trans (pushed.readW (w := 32) (Region.contains_self _ _)
    (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact separate) (by decide))

end VG.Proof.RsaKeyGen.X86.Key
