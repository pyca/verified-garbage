module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateFinishInput
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateFinish
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.RsaKeyGen.RandMemory
import VerifiedGarbage.Proof.Framework.Offset

/-! # The native finish paths expose exact status, output bytes, and entropy consumption -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86

def Outputs (E : Environment) (status count : Nat) (bytes : List Byte) (s : State) : Prop :=
  s.gpr .eax = BitVec.ofNat 32 status ∧ Spec.Rsa.bytesAt s.mem (E.out.setWidth 64) E.length = bytes ∧
  s.mem.readW (E.used.setWidth 64) 64 = BitVec.ofNat 64 count

theorem FinishReady.keepMem {E : Environment} {c : Nat} {s t : State} (S : FinishReady E c s)
    (M : t.mem = s.mem) {regs : List Reg} (K : Keeps regs s t) (base : .edi ∉ regs) (sp : .esp ∉ regs) :
    FinishReady E c t := by
  obtain ⟨S, zeros⟩ := S
  refine ⟨⟨S.scratch.of_keeps K base sp, S.positive, S.space, S.header, ?_, ?_, ?_, rfl, ?_, S.outFit, ?_,
    S.usedWrite.of_keeps K, S.workspaceFar, S.usedFar⟩, ?_⟩
  · rw [M]; exact S.outEq
  · rw [M]; exact S.lengthEq
  · rw [M]; exact S.usedEq
  · rw [M]; exact S.candidateEq
  · rw [K.2.2]; exact S.outWrite
  · rw [M]; exact zeros

theorem used_frame {E : Environment} {m m' : Mem} (O : Outside (E.used.setWidth 64) 0 8 m m') :
    MutableFrame E m m' := by
  have F := VG.Proof.Bignum.outside_frame O (by decide)
  change Frame [⟨off (E.used.setWidth 64) 0, 8⟩] m m' at F
  have base : off (E.used.setWidth 64) 0 = E.used.setWidth 64 := by rw [off, BitVec.add_zero]
  rw [base] at F
  exact F.mono (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self))

theorem finish_used_ok {E : Environment} (v : E.Valid) {c status : Nat} {s : State} (S : FinishReady E c s) :
    WP isa (VG.Impl.RsaKeyGen.X86.CandidateFinish.used status) s fun t =>
      Outputs E status (w32 s.mem E.base 152) (List.replicate E.length 0) t ∧
      MutableFrame E s.mem t.mem ∧ Keeps WitnessStep.clob s t := by
  refine WP.mono (CandidateFinish.used_ok S.1.scratch S.1.header S.1.usedWrite S.1.usedEq rfl)
    fun t ⟨statusEq, memory, O, K⟩ => ?_
  refine ⟨⟨statusEq, ?_, ?_⟩, used_frame O, K.mono (by unfold WitnessStep.clob; decide)⟩
  · exact (VG.Proof.Bignum.scratch_bytes O (by have := v.outFit; omega) v.outUsed).trans S.2
  · rw [memory, Mem.readW_writeW_self64]

theorem finish_none_ok {E : Environment} (v : E.Valid) {c : Nat} {s : State} (S : FinishReady E c s) :
    WP isa VG.Impl.RsaKeyGen.X86.CandidateFinish.none s fun t =>
      Outputs E 0 0 (List.replicate E.length 0) t ∧
      MutableFrame E s.mem t.mem ∧ Keeps WitnessStep.clob s t := by
  refine WP.mono (CandidateFinish.none_ok S.1.scratch (by have := S.1.header; omega) S.1.usedWrite S.1.usedEq)
    fun t ⟨statusEq, memory, O, K⟩ => ?_
  refine ⟨⟨statusEq, ?_, ?_⟩, used_frame O, K.mono (by unfold WitnessStep.clob; decide)⟩
  · exact (VG.Proof.Bignum.scratch_bytes O (by have := v.outFit; omega) v.outUsed).trans S.2
  · rw [memory, Mem.readW_writeW_self64]

theorem finish_prime_ok {E : Environment} (v : E.Valid) {c : Nat} {s : State} (S : FinishReady E c s) :
    WP isa (VG.Impl.RsaKeyGen.X86.CandidateFinish.prime E.width) s fun t =>
      Outputs E 1 (w32 s.mem E.base 152) (Spec.Rsa.i2osp c E.length) t ∧
      MutableFrame E s.mem t.mem ∧ Keeps WitnessStep.clob s t := by
  refine WP.mono (CandidateFinish.prime_ok S.1) fun t ⟨statusEq, bytes, used, F, K⟩ => ?_
  rw [v.length_eq] at bytes F
  refine ⟨⟨statusEq, bytes, used⟩, F.mono ?_, K.mono (by unfold WitnessStep.clob; decide)⟩
  intro r mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · exact List.mem_append_left _ List.mem_cons_self
  · exact List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self)

end VG.Proof.RsaKeyGen.X86.Candidate
