module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTCandidateScreenP
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTResidue
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTTrialBuffers
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateBuffers
import VerifiedGarbage.Proof.Bignum.OctetsValue
import VerifiedGarbage.Proof.Bignum.Octets

/-! Equal public candidate values give identical generator-residue traces. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two)

theorem candidateResidue_ct : RelCT isa (Two ScreenPStart)
    VG.Impl.Ffdh.Arm.ParameterCandidate.residue (fun _ _ => True) := by
  intro s t trS trT u v h runS runT
  obtain ⟨p, left, right, sp⟩ := h
  let xs := Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length
  have length : xs.length = p.length := VG.Proof.Bignum.bytesAt_length _ _ _
  have same : Spec.Rsa.bytesAt t.mem (State.addr p.out) p.length = xs :=
    VG.Proof.Bignum.bytesAt_eq_of_value length (right.number.trans left.number.symm)
  have buffersL := trialBuffers_of_octets (xs := xs) (prime := 0#32) left.context.read_context length rfl
  have buffersR := trialBuffers_of_octets (xs := xs) (prime := 0#32) right.context.read_context length same
  have genL : s.mem.readW (State.addr (s.sp + 28#32)) 32 = BitVec.ofNat 32 p.generator := by
    simpa only [candidateValues] using left.context.saved.saved 28 (by simp [candidateSlots])
  have genR : t.mem.readW (State.addr (t.sp + 28#32)) 32 = BitVec.ofNat 32 p.generator := by
    simpa only [candidateValues] using right.context.saved.saved 28 (by simp [candidateSlots])
  exact residue_ct _ _ _ _ _ _ ⟨(⟨p.out, p.length, 0#32, xs.reverse⟩, p.generator), ⟨buffersL, p.generatorAllowed, genL⟩,
    ⟨buffersR, p.generatorAllowed, genR⟩, sp⟩ runS runT

end VG.Proof.Ffdh.Arm.ParameterCandidate
