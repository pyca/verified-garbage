module
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Dsa.X86.Generation.TapeMemory
public import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialTable
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ArenaReady
public import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameWords
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometryBuffers
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometrySeparate
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometryStack

/-! # Shared search state preserves immutable tapes, trial constants, and saved arguments -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Generation.Layout

def parameterMutableSlots : List Nat := [0, 1, 2, 10, 16, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36]

def parameterWrites (G : GenerationGeometry) : List Region :=
  [G.part VG.Impl.Dsa.Generation.Layout.hash (usedBytes G.pLen - VG.Impl.Dsa.Generation.Layout.hash),
   ⟨G.frameBase, VG.Impl.Dsa.X86.Generation.frameBytes⟩, below G.frame 128]

structure SearchContextPlan where
  geometry : GenerationGeometry
  seeds : GenerationTape geometry
  hs : GenerationTape geometry
  witnesses : GenerationTape geometry
  saved : Nat → BitVec 32
  wrapped : saved 3 = geometry.pointer wrappedSeed
  hashesValue : saved 4 = geometry.pointer hashes
  parent : saved 5 = geometry.parent
  seedPointer : saved 8 = seeds.pointer
  seedLength : saved 9 = BitVec.ofNat 32 seeds.bytes.length
  hPointer : saved 11 = hs.pointer
  hLength : saved 12 = BitVec.ofNat 32 hs.bytes.length
  witnessPointer : saved 13 = witnesses.pointer
  witnessLength : saved 15 = BitVec.ofNat 32 witnesses.bytes.length
  hashPointer : saved 14 = geometry.pointer VG.Impl.Dsa.Generation.Layout.hash
  pLength : saved 17 = BitVec.ofNat 32 geometry.pLen
  qLength : saved 18 = BitVec.ofNat 32 geometry.qLen

structure SearchContext (P : SearchContextPlan) (W : Nat → BitVec 32) (s : State) : Prop where
  arena : ArenaReady P.geometry s
  representation : FrameWords s.mem P.geometry.frameBase W
  fixed : ∀ i < 37, i ∉ parameterMutableSlots → W i = P.saved i
  table : TrialTableReady s.mem P.geometry.base 1024
  seeds : TapeMemory P.seeds s
  hs : TapeMemory P.hs s
  witnesses : TapeMemory P.witnesses s

theorem GenerationTape.parameterApart {G : GenerationGeometry} (T : GenerationTape G) :
    ∀ r ∈ parameterWrites G, (⟨T.pointer.setWidth 64, T.bytes.length⟩ : Region).Disjoint r := by
  intro r hr
  simp only [parameterWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · apply T.part
    unfold VG.Impl.Dsa.Generation.Layout.hash usedBytes domainCheck
    omega
  · exact T.frame
  · exact T.below (Nat.le_refl _)

theorem GenerationGeometry.tableApart (G : GenerationGeometry) :
    ∀ r ∈ parameterWrites G, (⟨G.base, 8192⟩ : Region).Disjoint r := by
  have room : 0 + 8192 ≤ usedBytes G.pLen := by unfold usedBytes domainCheck; omega
  have same : (⟨G.base, 8192⟩ : Region) = G.part 0 8192 := by
    simp only [GenerationGeometry.part, off, BitVec.add_zero]
  rw [same]
  intro r hr
  simp only [parameterWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · apply G.parts_disjoint room
    · unfold VG.Impl.Dsa.Generation.Layout.hash usedBytes domainCheck; omega
    · exact .inl (by unfold VG.Impl.Dsa.Generation.Layout.hash; decide)
  · exact (G.frame_part room).symm
  · exact (G.stack_part_native room (Nat.le_refl _)).symm

theorem SearchContext.frame {P : SearchContextPlan} {W W' : Nat → BitVec 32} {s t : State} {regs : List Reg}
    (R : SearchContext P W s) (rep : FrameWords t.mem P.geometry.frameBase W')
    (fixed : ∀ i < 37, i ∉ parameterMutableSlots → W' i = W i)
    (O : Frame (parameterWrites P.geometry) s.mem t.mem) (K : Keeps regs s t) (sp : .esp ∉ regs) :
    SearchContext P W' t := by
  have tableWord (d : Nat) (hd : d + 4 ≤ 8192) :
      t.mem.readW (off P.geometry.base d) 32 = s.mem.readW (off P.geometry.base d) 32 :=
    O.readW (r := ⟨P.geometry.base, 8192⟩) (Offset.contains_base _ hd (by omega)) P.geometry.tableApart (by decide)
  exact ⟨R.arena.keep K sp, rep, fun i hi hx => (fixed i hi hx).trans (R.fixed i hi hx),
    ⟨fun i hi => (tableWord (8 * i) (by omega)).trans (R.table.prime i hi),
     fun i hi => (tableWord (8 * i + 4) (by omega)).trans (R.table.reciprocal i hi)⟩,
    R.seeds.keep O P.seeds.parameterApart K, R.hs.keep O P.hs.parameterApart K,
    R.witnesses.keep O P.witnesses.parameterApart K⟩

theorem SearchContext.congr {P : SearchContextPlan} {W : Nat → BitVec 32} {s t : State} {regs : List Reg}
    (R : SearchContext P W s) (mem : t.mem = s.mem) (K : Keeps regs s t) (sp : .esp ∉ regs) : SearchContext P W t :=
  R.frame (by rw [mem]; exact R.representation) (fun _ _ _ => rfl) (by rw [mem]; exact Frame.refl _ _) K sp

theorem SearchContext.relabel {P : SearchContextPlan} {W W' : Nat → BitVec 32} {s : State}
    (R : SearchContext P W s) (rep : FrameWords s.mem P.geometry.frameBase W') : SearchContext P W' s :=
  R.frame rep (fun i hi _ => (rep i hi).symm.trans (R.representation i hi))
    (Frame.refl _ _) (Keeps.refl [] _) (by decide)
end VG.Proof.Dsa.X86.Generation
