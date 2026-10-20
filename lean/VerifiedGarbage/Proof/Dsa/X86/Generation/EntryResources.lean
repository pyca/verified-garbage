module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.EntryPlan
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchStorage

/-! # Preserve caller tapes while populating the persistent argument frame -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

structure EntryResources {s : State} (A : ParameterABI s) (t : State) : Prop where
  arena : ArenaReady A.geometry t
  arguments : EntryArguments A.geometry.frameBase (arg s) t
  tableWrite : (⟨A.geometry.base, 8192⟩ : Region) ∈ t.wr
  seeds : TapeMemory A.seeds t
  hs : TapeMemory A.hs t
  witnesses : TapeMemory A.witnesses t

theorem entryStorage_ok {s t : State} {A : ParameterABI s} {W : Nat → BitVec 32}
    (R : EntryResources A t) (words : FrameWords t.mem A.geometry.frameBase W) :
    WP isa (.block (entryIncoming ++ entryDerived)) t fun u =>
      SearchStorage (A.plan W) (initialWords (arg s) W) u ∧
      Frame [⟨A.geometry.frameBase, VG.Impl.Dsa.X86.Generation.frameBytes⟩] t.mem u.mem ∧ Keeps [.eax] t u := by
  refine WP.mono (entryInitialize_ok R.arguments words) fun u ⟨_, Wu, O, K⟩ => ?_
  refine ⟨⟨R.arena.keep K (by decide), Wu, fun _ _ _ => rfl,
    by rw [K.2.2]; exact R.tableWrite, ?_, ?_, ?_⟩, O, K⟩
  · exact R.seeds.keep O (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact A.seeds.frame) K
  · exact R.hs.keep O (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact A.hs.frame) K
  · exact R.witnesses.keep O (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact A.witnesses.frame) K
end VG.Proof.Dsa.X86.Generation
