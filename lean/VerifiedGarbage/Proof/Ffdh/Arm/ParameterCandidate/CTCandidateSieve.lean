module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTCandidateTest
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.Table
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTSieve
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateTable
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateSieveMath
import VerifiedGarbage.Proof.Bignum.OctetsValue
import VerifiedGarbage.Proof.Bignum.Octets

/-! Reuse the native RSA sieve timing proof for either public candidate modulus. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch

structure CandidateSieveStart (q : Bool) (p : CandidatePoint) (s : State) : Prop where
  context : CandidateContext p.params p.used s
  table : TableData p.params.base p.params.length s.mem
  number : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr p.params.out) p.params.length) = (candidatePhase p.params q).modulus
  odd : (candidatePhase p.params q).modulus % 2 = 1

structure CandidateSieved (q : Bool) (p : CandidatePoint) (s : State) : Prop where
  start : CandidateSieveStart q p s
  zero : s.z = Spec.Ffdh.primeShape (candidatePhase p.params q).modulus

theorem candidateSieved_ok (q : Bool) (p : CandidatePoint) (s : State) (h : CandidateSieveStart q p s) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.sieve s (CandidateSieved q p) := by
  have large : 8161 < (candidatePhase p.params q).modulus := by
    cases q
    · exact p.params.sieve_large.1
    · exact p.params.sieve_large.2
  refine WP.mono (candidateSieve_ok h.context h.table (by rw [h.number]; exact large) (by rw [h.number]; exact h.odd)) ?_
  rintro t ⟨ctx, table, zero, bytes, _, _⟩
  rw [h.number] at zero
  exact ⟨⟨ctx, table, by rw [bytes]; exact h.number, h.odd⟩, zero⟩

theorem candidateSieve_ct (q : Bool) : RelCT isa (Two (CandidateSieveStart q))
    VG.Impl.Ffdh.Arm.ParameterCandidate.sieve (Two (CandidateSieved q)) := by
  refine two_post ?_ (candidateSieved_ok q)
  intro s t trS trT u v h runS runT
  obtain ⟨p, left, right, sp⟩ := h
  let xs := Spec.Rsa.bytesAt s.mem (State.addr p.params.out) p.params.length
  have length : xs.length = p.params.length := VG.Proof.Bignum.bytesAt_length _ _ _
  have same : Spec.Rsa.bytesAt t.mem (State.addr p.params.out) p.params.length = xs :=
    VG.Proof.Bignum.bytesAt_eq_of_value length (right.number.trans left.number.symm)
  have leftPublic : SievePublic ⟨p.params.out, p.params.base, xs⟩ s := by
    change SieveContext p.params.out p.params.base xs.length s ∧ _
    rw [length]
    exact ⟨left.context.sieve_context left.table, rfl⟩
  have rightPublic : SievePublic ⟨p.params.out, p.params.base, xs⟩ t := by
    change SieveContext p.params.out p.params.base xs.length t ∧ _
    rw [length]
    exact ⟨right.context.sieve_context right.table, same⟩
  exact sieve_ct _ _ _ _ _ _ ⟨_, leftPublic, rightPublic, sp⟩ runS runT

end VG.Proof.Ffdh.Arm.ParameterCandidate
