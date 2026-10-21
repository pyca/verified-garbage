module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTCandidateTest
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.Table
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTPairSieve
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidatePair
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateTable
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidatePairMath
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateSieveMath
import VerifiedGarbage.Proof.Bignum.OctetsValue
import VerifiedGarbage.Proof.Bignum.Octets

/-! Reuse the paired sieve timing proof without allocating a separate q buffer. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch

structure CandidatePairStart (p : CandidatePoint) (s : State) : Prop where
  context : CandidateContext p.params p.used s
  table : TableData p.params.base p.params.length s.mem
  number : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr p.params.out) p.params.length) = p.params.candidate
  oddQ : ((p.params.candidate-1)/2)%2=1

structure CandidatePaired (p : CandidatePoint) (s : State) : Prop where
  start : CandidatePairStart p s
  zero : s.z=candidateShapes p.params

theorem candidatePaired_ok (p : CandidatePoint) (s : State) (h : CandidatePairStart p s) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.pairSieve s (CandidatePaired p) := by
  refine WP.mono (candidatePair_ok h.context h.table h.number h.oddQ) ?_
  rintro t ⟨ctx, table, zero, bytes, _, _⟩
  exact ⟨⟨ctx, table, by rw [bytes]; exact h.number, h.oddQ⟩, zero⟩

theorem candidatePair_ct : RelCT isa (Two (CandidatePairStart))
    VG.Impl.Ffdh.Arm.ParameterCandidate.pairSieve (Two (CandidatePaired)) := by
  refine two_post ?_ (candidatePaired_ok)
  intro s t trS trT u v h runS runT
  obtain ⟨p, left, right, sp⟩ := h
  let xs := Spec.Rsa.bytesAt s.mem (State.addr p.params.out) p.params.length
  have length : xs.length = p.params.length := VG.Proof.Bignum.bytesAt_length _ _ _
  have same : Spec.Rsa.bytesAt t.mem (State.addr p.params.out) p.params.length = xs :=
    VG.Proof.Bignum.bytesAt_eq_of_value length (right.number.trans left.number.symm)
  have leftPublic : PairPublic ⟨p.params.out, p.params.base, xs⟩ s := by
    change SieveContext p.params.out p.params.base xs.length s ∧ _
    rw [length]
    exact ⟨left.context.sieve_context left.table, rfl⟩
  have rightPublic : PairPublic ⟨p.params.out, p.params.base, xs⟩ t := by
    change SieveContext p.params.out p.params.base xs.length t ∧ _
    rw [length]
    exact ⟨right.context.sieve_context right.table, same⟩
  exact pairSieve_ct _ _ _ _ _ _ ⟨_, leftPublic, rightPublic, sp⟩ runS runT

end VG.Proof.Ffdh.Arm.ParameterCandidate
