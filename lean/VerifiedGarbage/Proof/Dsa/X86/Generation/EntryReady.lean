module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.EntryStart
public import VerifiedGarbage.Proof.Dsa.X86.Generation.EntryResources
import VerifiedGarbage.Proof.Dsa.X86.Generation.EntryCoordinates

/-! # The narrowed inner-entry state supplies all immutable tapes and frame arguments -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Generation.Layout

theorem EntryStart.resources {s t : State} {A : ParameterABI s} (R : EntryStart A t) :
    EntryResources A (t.withRegions s.rd (bodyWrites A)) := by
  have F : SearchFrame (t.withRegions s.rd (bodyWrites A)) A.geometry.frameBase :=
    ⟨by change (t.gpr .esp).setWidth 64 = _; rw [R.esp]; rfl,
     List.mem_cons_self, A.geometry.frameBound⟩
  refine ⟨⟨F, R.esp, by simp [bodyWrites], by simp [bodyWrites], by simp [bodyWrites]⟩,
    ⟨F, A.entryBound, ?_, ?_⟩, by simp [bodyWrites], ?_, ?_, ?_⟩
  · intro j hj
    rw [A.argAddress hj]
    exact ⟨_, List.mem_append_right _ (by simp [bodyWrites]), A.argsContains hj⟩
  · intro j hj
    change t.mem.readW _ 32 = arg s j
    rw [A.argAddress hj]
    exact R.memory.readW (A.argsContains hj)
      (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact A.argsStack) (by decide)
  · apply entryTapeMemory R
    · simp only [ParameterABI.seeds, ParameterABI.tape, Spec.Rsa.bytesAt, List.length_map, List.length_range, A.rd]
      exact List.mem_cons_self
    · simp only [ParameterABI.seeds, ParameterABI.tape, Spec.Rsa.bytesAt, List.length_map, List.length_range]
    · simpa only [ParameterABI.seeds, ParameterABI.tape, Spec.Rsa.bytesAt, List.length_map, List.length_range] using A.stackSeeds.symm
  · apply entryTapeMemory R
    · simp only [ParameterABI.hs, ParameterABI.tape, Spec.Rsa.bytesAt, List.length_map, List.length_range, A.rd]
      exact List.mem_cons_of_mem _ List.mem_cons_self
    · simp only [ParameterABI.hs, ParameterABI.tape, Spec.Rsa.bytesAt, List.length_map, List.length_range]
    · simpa only [ParameterABI.hs, ParameterABI.tape, Spec.Rsa.bytesAt, List.length_map, List.length_range] using A.stackHs.symm
  · apply entryTapeMemory R
    · simp only [ParameterABI.witnesses, ParameterABI.tape, Spec.Rsa.bytesAt, List.length_map, List.length_range, A.rd]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
    · simp only [ParameterABI.witnesses, ParameterABI.tape, Spec.Rsa.bytesAt, List.length_map, List.length_range]
    · simpa only [ParameterABI.witnesses, ParameterABI.tape, Spec.Rsa.bytesAt, List.length_map, List.length_range] using A.stackWitnesses.symm
end VG.Proof.Dsa.X86.Generation
