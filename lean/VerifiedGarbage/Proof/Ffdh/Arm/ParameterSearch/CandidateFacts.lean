module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CallPost
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CallParams
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Packed
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.EntropyRequest
import VerifiedGarbage.Proof.Ffdh.SievedBounds
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Stream
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Bounds
public import VerifiedGarbage.Spec.Ffdh.SievedGeneration

/-! ### `Ffdh.Arm.ParameterSearch.Result`, which this module and modules that import it used -/

section

/-! Each native transition preserves the shared complete-search result. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Spec.Ffdh VG.Proof.Ffdh.SievedGeneration VG.Proof.Ffdh.ParameterCandidate

theorem candidateUsed_bound (p : SearchParams) (used : Nat) :
    candidateUsed p used ≤ p.c.bytes.length - used := by
  unfold candidateUsed
  split <;> omega_using []

theorem candidate_short (p : SearchParams) (used : Nat)
    (short : p.c.bytes.length - used < p.c.length) : candidateResult p used = none := by
  unfold candidateResult
  unfold Spec.Ffdh.sievedParameterCandidate
  have draw := draw_of_short (r := p.c.bytes.drop used) (len := p.c.length)
    (by simpa only [List.length_drop] using short)
  change VG.Spec.RsaKeyGen.draw ((p.c.bits + 7) / 8) (p.c.bytes.drop used) = none at draw
  rw [draw]
  rfl

theorem SearchParams.tail_short {p : SearchParams} {used remaining : Nat} (positive : 0 < remaining)
    (candidate : candidateResult p used = none) :
    p.tail used remaining = if Spec.Ffdh.parameterEntropy p.c.bits ≤ p.c.bytes.length - used
      then .exhausted used else .entropy remaining (p.c.bytes.length - used) used := by
  cases remaining with
  | zero => omega
  | succ n =>
    unfold SearchParams.tail
    rw [sievedParameterSearch]
    change sievedParameterCandidate p.c.bits p.c.generator (p.c.bytes.drop used) = _ at candidate
    rw [candidate]
    simp only [List.length_drop]
    split <;> rfl

theorem SearchParams.tail_accept {p : SearchParams} {used remaining prime : Nat}
    {rest : VG.Spec.RsaKeyGen.Rand} (positive : 0 < remaining)
    (candidate : candidateResult p used = some (some prime, rest)) :
    p.tail used remaining = .accepted prime (used + candidateUsed p used) := by
  cases remaining with
  | zero => omega
  | succ n =>
    unfold SearchParams.tail
    rw [sievedParameterSearch]
    change sievedParameterCandidate p.c.bits p.c.generator (p.c.bytes.drop used) = _ at candidate
    rw [candidate]
    simp only [List.length_drop, ParameterSearchResult.consume, candidateUsed, candidateResult, candidate]

theorem SearchParams.tail_reject {p : SearchParams} {used remaining : Nat}
    {rest : VG.Spec.RsaKeyGen.Rand} (positive : 0 < remaining)
    (candidate : candidateResult p used = some (none, rest)) :
    p.tail used remaining = p.tail (used + candidateUsed p used) (remaining - 1) := by
  have step := search_reject positive candidate
  simpa only [SearchParams.tail, candidateUsed, candidate, List.length_drop] using step

end VG.Proof.Ffdh.Arm.ParameterSearch

end

end

/-! The candidate's public result supplies the exact native consumption field and classification. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Mont VG.Proof.X25519.Arm
open VG.Proof.Ffdh.Arm.KeySearch (lowWord)

theorem CandidatePost.consumed_low {p : SearchParams} {used : Nat} {s : State}
    (post : CandidatePost p used s) : lowWord s.mem p.control 14 = BitVec.ofNat 32 (candidateUsed p used) := by
  have result := post.consumed
  change [s.mem.readW (State.addr (p.control + 112#32) + 0#64) 64] =
    [BitVec.ofNat 64 (candidateUsed p used)] at result
  rw [BitVec.add_zero, List.singleton_inj, p.used_addr] at result
  exact packedLow s.mem p.control 14 (candidateUsed p used)
    (by have := candidateUsed_bound p used; have := p.c.tapeCount; omega_arith) result

theorem CandidatePost.after_read {p : SearchParams} {used : Nat} {s t : State} {rs : List Reg}
    (post : CandidatePost p used s) (mem : t.mem = s.mem) (rest : Rest rs s t) (kept : .r0 ∉ rs) :
    CandidatePost p used t :=
  ⟨by rw [rest.gpr .r0 kept]; exact post.status, by rw [mem]; exact post.output,
    by rw [mem]; exact post.consumed⟩

end VG.Proof.Ffdh.Arm.ParameterSearch
