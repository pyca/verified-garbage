module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchContext
import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameMemory
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometrySeparate

/-! # Search resources before initializing the public divisor table -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Generation.Layout

structure SearchStorage (P : SearchContextPlan) (W : Nat → BitVec 32) (s : State) : Prop where
  arena : ArenaReady P.geometry s
  representation : FrameWords s.mem P.geometry.frameBase W
  fixed : ∀ i < 37, i ∉ parameterMutableSlots → W i = P.saved i
  tableWrite : (⟨P.geometry.base, 8192⟩ : Region) ∈ s.wr
  seeds : TapeMemory P.seeds s
  hs : TapeMemory P.hs s
  witnesses : TapeMemory P.witnesses s

theorem SearchStorage.keep {P : SearchContextPlan} {W : Nat → BitVec 32} {s t : State} {rs : List Reg}
    (R : SearchStorage P W s)
    (O : Frame [⟨P.geometry.base, usedBytes P.geometry.pLen⟩] s.mem t.mem)
    (K : Keeps rs s t) (sp : .esp ∉ rs) : SearchStorage P W t := by
  have frameApart : (⟨P.geometry.frameBase, VG.Impl.Dsa.X86.Generation.frameBytes⟩ : Region).Disjoint
      ⟨P.geometry.base, usedBytes P.geometry.pLen⟩ := by
    have h := P.geometry.frame_part (d := 0) (n := usedBytes P.geometry.pLen) (by omega)
    simpa only [GenerationGeometry.part, off, BitVec.add_zero] using h
  exact ⟨R.arena.keep K sp,
    R.representation.keep O (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact frameApart),
    R.fixed, by rw [K.2.2]; exact R.tableWrite,
    R.seeds.keep O (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact P.seeds.arena) K,
    R.hs.keep O (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact P.hs.arena) K,
    R.witnesses.keep O (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact P.witnesses.arena) K⟩

theorem SearchStorage.context {P : SearchContextPlan} {W : Nat → BitVec 32} {s : State}
    (R : SearchStorage P W s) (table : TrialTableReady s.mem P.geometry.base 1024) : SearchContext P W s :=
  ⟨R.arena, R.representation, R.fixed, table, R.seeds, R.hs, R.witnesses⟩
end VG.Proof.Dsa.X86.Generation
