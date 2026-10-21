module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateLoadInput
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateMemory

/-! # Register and flag operations retain the drawn candidate and input snapshots -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont.X86

theorem Input.keepMem {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s t : State}
    (I : Input E eBytes pBytes entropy s) (M : t.mem = s.mem) {regs : List Reg} (K : Keeps regs s t)
    (base : .edi ∉ regs) (sp : .esp ∉ regs) (syms : t.syms = s.syms) : Input E eBytes pBytes entropy t := by
  have F : WorkFrame E s.mem t.mem := by rw [M]; exact Frame.refl _ _
  refine I.keep v K base sp F ?_ ?_ (by rw [syms])
  · intro i index; rw [M]; exact I.header i index
  · rw [M]; exact I.usedPointer

theorem Drawn.keepMem {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s t : State}
    (D : Drawn E eBytes pBytes entropy s) (M : t.mem = s.mem) {regs : List Reg} (K : Keeps regs s t)
    (base : .edi ∉ regs) (sp : .esp ∉ regs) (syms : t.syms = s.syms) : Drawn E eBytes pBytes entropy t := by
  have F : WorkFrame E s.mem t.mem := by rw [M]; exact Frame.refl _ _
  refine ⟨D.input.keep v K base sp F ?_ ?_ (by rw [syms]), ?_, ?_, ?_⟩
  · intro i index; rw [M]; exact D.input.header i index
  · rw [M]; exact D.input.usedPointer
  · rw [M]; exact D.candidate
  · rw [M]; exact D.used
  · rw [M]; exact D.zeros

end VG.Proof.RsaKeyGen.X86.Candidate
