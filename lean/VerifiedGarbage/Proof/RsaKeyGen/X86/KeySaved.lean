module

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCallArgs
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCallValid
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyGeometry
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Mont.X86.Compact.Frame
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCallGeometry

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

end VG.Proof.RsaKeyGen.X86.Key
