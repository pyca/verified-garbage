module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.GeneratorSearchPlan
import VerifiedGarbage.Proof.Dsa.X86.Generation.DrawMemory
import VerifiedGarbage.Proof.Dsa.X86.Generation.SampleMemory
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PreparedContext

/-! # Stable generator-search memory and the three mutable frame slots -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

structure GeneratorSearchMemory (P : GeneratorSearchPlan) (W : Nat → BitVec 32) (s : State) : Prop where
  prepared : PrimePrepared P.core s
  layout : SearchFrame s P.frame
  representation : FrameWords s.mem P.frame W
  fixed : ∀ i < 37, i ∉ [0, 2, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36] → W i = P.saved i
  tapeValue : Spec.Rsa.bytesAt s.mem (P.tapePtr.setWidth 64) P.tape.length = P.tape
  exponentValue : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((generatorExponentPointer P.parent).setWidth 64) P.core.len) =
    (P.core.modulus - 1) / P.q
  tapeRead : ∀ d k, d + k ≤ P.tape.length → InRegions (s.rd ++ s.wr) (off (P.tapePtr.setWidth 64) d) k
  exponentRead : ∀ d, d + 4 ≤ P.core.len → InRegions (s.rd ++ s.wr)
    (off ((generatorExponentPointer P.parent).setWidth 64) d) 4
  outputWrite : ∀ d k, d + k ≤ P.core.len → InRegions s.wr
    (off ((generatorOutputPointer P.parent).setWidth 64) d) k

theorem GeneratorSearchMemory.frame {P : GeneratorSearchPlan} {W W' : Nat → BitVec 32} {s t : State} {regs : List Reg}
    (R : GeneratorSearchMemory P W s) (prepared : PrimePrepared P.core t)
    (rep : FrameWords t.mem P.frame W')
    (fixed : ∀ i < 37, i ∉ [0, 2, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36] → W' i = W i)
    (O : Frame P.changed s.mem t.mem) (K : Keeps regs s t) (sp : .esp ∉ regs) : GeneratorSearchMemory P W' t := by
  exact ⟨prepared, R.layout.keeps K sp, rep,
    fun i hi hx => (fixed i hi hx).trans (R.fixed i hi hx),
    (drawFrame_bytes O P.tapeSeparate (by have := P.tapeFits; omega)).trans R.tapeValue,
    by rw [drawFrame_bytes O P.exponentSeparate (by have := P.core.lenMax; omega), R.exponentValue],
    by intro d k hk; rw [K.2.1, K.2.2]; exact R.tapeRead d k hk,
    by intro d hd; rw [K.2.1, K.2.2]; exact R.exponentRead d hd,
    by intro d k hk; rw [K.2.2]; exact R.outputWrite d k hk⟩

theorem GeneratorSearchMemory.congr {P : GeneratorSearchPlan} {W : Nat → BitVec 32} {s t : State} {regs : List Reg}
    (R : GeneratorSearchMemory P W s) (mem : t.mem = s.mem) (K : Keeps regs s t) (sp : .esp ∉ regs) :
    GeneratorSearchMemory P W t := by
  exact R.frame (R.prepared.frame (by rw [mem]; exact Frame.refl [] s.mem) (by simp) K sp)
    (by rw [mem]; exact R.representation) (fun _ _ _ => rfl)
    (by rw [mem]; exact Frame.refl _ _) K sp

theorem GeneratorSearchMemory.relabel {P : GeneratorSearchPlan} {W W' : Nat → BitVec 32} {s : State}
    (R : GeneratorSearchMemory P W s) (rep : FrameWords s.mem P.frame W') : GeneratorSearchMemory P W' s :=
  R.frame R.prepared rep (fun i hi _ => (rep i hi).symm.trans (R.representation i hi))
    (Frame.refl _ _) (Keeps.refl [] _) (by decide)

theorem generator_search_frame {P : GeneratorSearchPlan} {m m' : Mem} {d n : Nat}
    (O : Outside P.frame d n m m') (room : d + n ≤ frameBytes) : Frame P.changed m m' := by
  exact (sampleOutside_frame O (by unfold frameBytes at room; omega)).sub (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨⟨P.frame, frameBytes⟩, by simp [GeneratorSearchPlan.changed, generatorSearchWrites], Offset.sub_base _ room⟩)
theorem GeneratorSearchMemory.control {P : GeneratorSearchPlan} {W W' : Nat → BitVec 32}
    {s t : State} {regs : List Reg} {d n : Nat}
    (R : GeneratorSearchMemory P W s) (rep : FrameWords t.mem P.frame W')
    (fixed : ∀ i < 37, i ∉ [0, 2, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36] → W' i = W i)
    (O : Outside P.frame d n s.mem t.mem) (room : d + n ≤ frameBytes)
    (K : Keeps regs s t) (sp : .esp ∉ regs) : GeneratorSearchMemory P W' t := by
  have F := copyOutside_frame (O.mono (o' := 0) (n' := frameBytes) (by omega) (by omega))
  have prepared := R.prepared.frame F (by
    intro r hr; obtain rfl := List.mem_singleton.mp hr; exact P.layout.frameScratch.symm) K sp
  exact R.frame prepared rep fixed (generator_search_frame O room) K sp
end VG.Proof.Dsa.X86.Generation
