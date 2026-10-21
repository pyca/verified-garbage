module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateParams
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateBuffers
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateMemory
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.Residue
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Framework.Omega

/-! The native residue check is exactly generationShape for the shaped candidate. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.X25519.Arm VG.Proof.Bignum.Arm

theorem CandidateParams.candidate_odd (p : CandidateParams) : p.candidate % 2 = 1 :=
  (VG.Proof.Ffdh.ParameterCandidate.candidate_shape (by have := p.minBits; omega) _).1

theorem CandidateParams.candidate_bits (p : CandidateParams) : Spec.RsaKeyGen.bitLength p.candidate = p.bits :=
  (VG.Proof.Ffdh.ParameterCandidate.candidate_bitLength (by have := p.minBits; omega) _).1

private theorem generationResidue (p : CandidateParams) :
    Spec.Ffdh.generationShape p.bits p.generator p.candidate =
      (if p.generator = 2 then decide (p.candidate % 24 = 11)
        else decide (p.candidate % 10 = 3 ∨ p.candidate % 10 = 7)) := by
  rcases p.generatorAllowed with generator | generator <;>
    simp [Spec.Ffdh.generationShape, p.minBits, p.maxBits, p.candidate_bits, generator, Bool.beq_eq_decide_eq]

theorem candidateResidue_ok {s : State} {p : CandidateParams} {consumed : Nat}
    (h : CandidateContext p consumed s)
    (number : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length) = p.candidate) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.residue s fun t =>
      CandidateContext p consumed t ∧ t.z = Spec.Ffdh.generationShape p.bits p.generator p.candidate ∧
      t.mem = s.mem ∧ Rest roundClobbers s t := by
  have generator : s.mem.readW (State.addr (s.sp + 28#32)) 32 = BitVec.ofNat 32 p.generator := by
    simpa only [candidateValues] using h.saved.saved 28 (by simp [candidateSlots])
  refine WP.mono (residue_ok h.read_context p.generatorAllowed generator (by rw [number]; exact p.candidate_odd)) ?_
  rintro t ⟨flag, memory, rest⟩
  rw [number, ← generationResidue p] at flag
  exact ⟨h.after_memory memory rest, flag, memory, rest.mono (by simp [roundClobbers])⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
