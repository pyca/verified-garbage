module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeFrameInputs
import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameMemory
import VerifiedGarbage.Proof.Dsa.X86.Generation.DrawMemory

/-! # Trial division preserves the persistent inputs to the prime engine -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

theorem PrimeFrameInputs.keep {G : PrimeConfig} {frame : Addr} {words : Nat → BitVec 32} {used : Nat}
    {s t : State} {rs : List Region} {regs : List Reg} (R : PrimeFrameInputs G frame words used s)
    (O : Frame rs s.mem t.mem) (K : Keeps regs s t) (sp : .esp ∉ regs)
    (frameApart : ∀ r ∈ rs, Region.Disjoint ⟨frame, frameBytes⟩ r)
    (candidateApart : ∀ r ∈ rs, Region.Disjoint ⟨(words 22).setWidth 64, G.len⟩ r) :
    PrimeFrameInputs G frame words used t := by
  exact ⟨R.search.keeps K sp, R.slots.keep O frameApart, R.base,
    by rw [K.2.2]; exact R.write, R.nowrap, by rw [K.1 _ sp]; exact R.stack,
    R.frameScratch, R.frameWitness, R.candidateFit,
    by intro d hd; rw [K.2.1, K.2.2]; exact R.candidateRead d hd,
    R.candidateScratch, by rw [drawFrame_bytes O candidateApart (by have := G.lenMax; omega)]; exact R.candidate,
    R.odd, R.gtOne, R.tape, R.tapeLen, R.usedValue, R.usedBound, R.witness,
    by intro i hi; rw [K.2.1, K.2.2]; exact R.tapeRead i hi,
    by intro d hd; rw [K.2.1, K.2.2]; exact R.witnessRead d hd,
    by intro i hi; rw [K.2.1, K.2.2]; exact R.witnessReadByte i hi,
    by intro i hi; rw [K.2.2]; exact R.witnessWrite i hi⟩
end VG.Proof.Dsa.X86.Generation
