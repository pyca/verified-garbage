module

import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateExponentStageTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateSieveLeak
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateScheduleContinue
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateSieveInput
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateFilterTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateDrawn
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateFinishReady
public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateFinish
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateEnvironment
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateLoadInput
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateTimingInput
public import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportContext
public import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinState
public import VerifiedGarbage.Spec.RsaKeyGen
public import VerifiedGarbage.TCB.X86.Isa

/-! # The shared leak controls sieve rejection and the complete remaining candidate path -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont.X86 VG.Proof.Dsa.X86 VG.Proof.RsaKeyGen

/-- After the code for the width: both runs wrote the same status, or both go
on with `eax = 4`, the drawn candidates neither too close nor divisible. -/
def FrontPair (E : Environment) (eBytes pBytes qBytes rBytes sBytes : List Byte) (s t : State) : Prop :=
  (s.gpr .eax = t.gpr .eax ∧ s.gpr .eax ≠ 4) ∨
  (s.gpr .eax = 4 ∧ t.gpr .eax = 4 ∧ DrawnPair E eBytes pBytes qBytes rBytes sBytes s t ∧
    Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime pBytes) (candidateValue E rBytes) = false ∧
    Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime qBytes) (candidateValue E sBytes) = false ∧
    Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E rBytes) = false ∧
    Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E sBytes) = false)

/-- A status written by both runs. -/
theorem drawn_done_trace {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (status : Nat) (small : status < 4) :
    RelCT isa (DrawnPair E eBytes pBytes qBytes rBytes sBytes)
      (VG.Impl.RsaKeyGen.X86.CandidateFinish.used status) (FrontPair E eBytes pBytes qBytes rBytes sBytes) := by
  refine ((drawn_used_trace v status).wp (F₁ := fun (u : State) => u.gpr .eax = BitVec.ofNat 32 status)
    (F₂ := fun (u : State) => u.gpr .eax = BitVec.ofNat 32 status) fun s t P =>
    ⟨WP.mono (finish_used_ok (status := status) v (P.left.finishReady v)) fun _ H => H.1.1,
      WP.mono (finish_used_ok (status := status) v (P.right.finishReady v)) fun _ H => H.1.1⟩).mono
    (fun _ _ P => P) ?_
  rintro u z ⟨_, U, Z⟩
  refine Or.inl ⟨U.trans Z.symm, ?_⟩
  rw [U]
  intro h
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at this
  rw [Nat.mod_eq_of_lt (by omega)] at this
  change status = 4 at this
  omega

end VG.Proof.RsaKeyGen.X86.Candidate
