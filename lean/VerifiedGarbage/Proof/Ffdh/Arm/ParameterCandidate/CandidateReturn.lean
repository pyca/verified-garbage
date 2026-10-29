module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateParams
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessEnd
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState

import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateBuffers
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.Finish
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ResultContext
import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.Status
/-! Candidate returns use the exact tape suffix, encoded p, and API status. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/Result.lean`, which only this module imported.
section

/-! Interpret the native phase status as the candidate API's output and count. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.X25519.Arm

def ResultPost (s : State) (dst usedPtr : BitVec 32) (n consumed status : Nat) (t : State) : Prop :=
  t.gpr .r0 = BitVec.ofNat 32 status ∧
  Spec.Rsa.wordsAt t.mem (State.addr usedPtr) 1 = [BitVec.ofNat 64 (if status = 0 then 0 else consumed)] ∧
  Spec.Rsa.bytesAt t.mem (State.addr dst) n =
    (if status = 1 then Spec.Rsa.bytesAt s.mem (State.addr dst) n else List.replicate n 0) ∧
  Frame [⟨State.addr dst, n⟩, ⟨State.addr usedPtr, 8⟩] s.mem t.mem ∧ Rest [.r0, .r1, .r2, .r3, .lr] s t

private theorem ResultPost.trans_pre {s u t : State} {dst usedPtr : BitVec 32} {n consumed status : Nat}
    (post : ResultPost u dst usedPtr n consumed status t) (memory : u.mem = s.mem) (rest : Rest [] s u) :
    ResultPost s dst usedPtr n consumed status t := by
  obtain ⟨result, words, bytes, changed, kept⟩ := post
  refine ⟨result, words, ?_, ?_, (rest.mono (by simp)).trans kept⟩
  · simpa only [memory] using bytes
  · simpa only [memory] using changed

private theorem resultTail_ok {s : State} {dst usedPtr : BitVec 32} {n consumed status : Nat}
    (h : ResultContext dst usedPtr n consumed s) (bound : status ≤ 2) (nonzero : status ≠ 0)
    (word : s.gpr .r3 = BitVec.ofNat 32 status) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterCandidate.seqs [
      .block [.cmp .r3 (.imm 1)], .ite .eq VG.Impl.Ffdh.Arm.ParameterCandidate.finAccepted
        VG.Impl.Ffdh.Arm.ParameterCandidate.finRejected]) s (ResultPost s dst usedPtr n consumed status) := by
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.seqs
  refine WP.seq (WP.mono (cmpStatus_ok status 1 (by omega) (by decide) word) ?_)
  rintro u ⟨⟨zero, memory⟩, rest⟩
  have ctx := h.after_memory memory rest
  by_cases one : status = 1
  · refine WP.seq (WP.ite true (by change some u.z = some true; rw [zero, decide_eq_true one]) ?_ (by intro h; cases h))
    intro _
    refine WP.mono (finAccepted_ok ctx) ?_
    intro t returned
    refine WP.block_nil ?_
    rw [one]
    exact (show ResultPost u dst usedPtr n consumed 1 t from returned).trans_pre memory rest
  · have two : status = 2 := by omega
    refine WP.seq (WP.ite false (by change some u.z = some false; rw [zero, decide_eq_false one]) (by intro h; cases h) ?_)
    intro _
    refine WP.mono (finRejected_ok ctx) ?_
    intro t returned
    refine WP.block_nil ?_
    rw [two]
    exact (show ResultPost u dst usedPtr n consumed 2 t from returned).trans_pre memory rest

theorem result_ok {s : State} {dst usedPtr : BitVec 32} {n consumed status : Nat}
    (h : ResultContext dst usedPtr n consumed s) (bound : status ≤ 2)
    (word : s.gpr .r3 = BitVec.ofNat 32 status) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.result s (ResultPost s dst usedPtr n consumed status) := by
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.result VG.Impl.Ffdh.Arm.ParameterCandidate.seqs
  refine WP.seq (WP.mono (cmpStatus_ok status 0 (by omega) (by decide) word) ?_)
  rintro u ⟨⟨zero, memory⟩, rest⟩
  have ctx := h.after_memory memory rest
  by_cases none : status = 0
  · refine WP.seq (WP.ite true (by change some u.z = some true; rw [zero, decide_eq_true none]) ?_ (by intro h; cases h))
    intro _
    refine WP.mono (finNone_ok ctx) ?_
    intro t returned
    refine WP.block_nil ?_
    rw [none]
    exact (show ResultPost u dst usedPtr n consumed 0 t from returned).trans_pre memory rest
  · refine WP.seq (WP.ite false (by change some u.z = some false; rw [zero, decide_eq_false none]) (by intro h; cases h) ?_)
    intro _
    refine WP.mono (resultTail_ok ctx bound none ((rest.gpr .r3 (by simp)).trans word)) ?_
    intro t returned
    refine WP.block_nil ?_
    exact returned.trans_pre memory rest

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.X25519.Arm

def candidateReturnRegions (p : CandidateParams) (sp : BitVec 32) : List Region :=
  ⟨State.addr p.usedPtr, 8⟩ :: candidateRegions p sp

def CandidateReturn (p : CandidateParams) (answer : Option (Bool × List Byte)) (s t : State) : Prop :=
  t.gpr .r0 = BitVec.ofNat 32 (witnessResultStatus answer) ∧
  Spec.Rsa.wordsAt t.mem (State.addr p.usedPtr) 1 =
    [BitVec.ofNat 64 (match answer with | none => 0 | some (_, rest) => p.bytes.length - rest.length)] ∧
  Spec.Rsa.bytesAt t.mem (State.addr p.out) p.length =
    (match answer with | some (true, _) => Spec.Rsa.i2osp p.candidate p.length | _ => List.replicate p.length 0) ∧
  Frame (candidateReturnRegions p s.sp) s.mem t.mem ∧ Rest roundClobbers s t

theorem witnessResultStatus_bound (answer : Option (Bool × List Byte)) : witnessResultStatus answer ≤ 2 := by
  cases answer with
  | none => decide
  | some pair => obtain ⟨pass, rest⟩ := pair; cases pass <;> simp only [witnessResultStatus] <;> omega

theorem CandidateReturn.trans_pre {s u t : State} {p : CandidateParams} {answer : Option (Bool × List Byte)}
    {rs : List Reg} (post : CandidateReturn p answer u t)
    (changed : Frame (candidateRegions p s.sp) s.mem u.mem) (rest : Rest rs s u)
    (clobbers : ∀ r ∈ rs, r ∈ roundClobbers) : CandidateReturn p answer s t := by
  obtain ⟨status, count, bytes, frame, restT⟩ := post
  rw [rest.sp] at frame
  exact ⟨status, count, bytes, (changed.mono (by intro r hr; exact List.mem_cons_of_mem _ hr)).trans frame,
    (rest.mono clobbers).trans restT⟩

private theorem candidateReturn_of_result {s : State} {p : CandidateParams} {used : Nat} {answer : Option (Bool × List Byte)}
    (h : CandidateContext p used s)
    (suffix : ∀ pass rest, answer = some (pass, rest) → rest = p.bytes.drop used)
    (number : ∀ rest, answer = some (true, rest) →
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length) = p.candidate) :
    ∀ t, ResultPost s p.out p.usedPtr p.length used (witnessResultStatus answer) t → CandidateReturn p answer s t := by
  rintro t ⟨result, words, bytes, changed, rest⟩
  refine ⟨result, ?_, ?_, changed.mono (by simp [candidateReturnRegions, candidateRegions]),
    rest.mono (by simp [roundClobbers])⟩
  · cases ha : answer with
    | none => simpa [ha, witnessResultStatus] using words
    | some pair =>
      obtain ⟨pass, tail⟩ := pair
      have tailEq := suffix pass tail ha
      change Spec.Rsa.wordsAt t.mem (State.addr p.usedPtr) 1 = [BitVec.ofNat 64 (p.bytes.length - tail.length)]
      rw [tailEq, List.length_drop]
      have usedEq : p.bytes.length - (p.bytes.length - used) = used := by have := h.consumedBound; omega
      rw [usedEq]
      cases pass <;> simpa [ha, witnessResultStatus] using words
  · cases ha : answer with
    | none => simpa [ha, witnessResultStatus] using bytes
    | some pair =>
      obtain ⟨pass, tail⟩ := pair
      cases pass with
      | false => simpa [ha, witnessResultStatus] using bytes
      | true =>
        have encoded := (VG.Proof.Rsa.i2osp_os2ip (Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length)).symm
        have size : (Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length).length = p.length := by simp [Spec.Rsa.bytesAt]
        rw [size, number tail ha] at encoded
        exact (show Spec.Rsa.bytesAt t.mem (State.addr p.out) p.length =
          Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length from by simpa [ha, witnessResultStatus] using bytes).trans encoded

theorem candidateResult_ok {s : State} {p : CandidateParams} {used : Nat} {answer : Option (Bool × List Byte)}
    (h : CandidateContext p used s)
    (status : s.gpr .r3 = BitVec.ofNat 32 (witnessResultStatus answer))
    (suffix : ∀ pass rest, answer = some (pass, rest) → rest = p.bytes.drop used)
    (number : ∀ rest, answer = some (true, rest) →
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length) = p.candidate) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.result s (CandidateReturn p answer s) :=
  WP.mono (result_ok h.result_context (witnessResultStatus_bound answer) status)
    (candidateReturn_of_result h suffix number)

theorem candidateRejected_ok {s : State} {p : CandidateParams} {used : Nat}
    (h : CandidateContext p used s) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.finRejected s
      (CandidateReturn p (some (false, p.bytes.drop used)) s) := by
  refine WP.mono (finRejected_ok h.result_context) ?_
  intro t returned
  exact candidateReturn_of_result h (by intro pass tail eq; cases eq; rfl)
    (by intro tail eq; cases eq) t returned

theorem candidateNone_ok {s : State} {p : CandidateParams} {used : Nat}
    (h : CandidateContext p used s) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.finNone s (CandidateReturn p none s) := by
  refine WP.mono (finNone_ok h.result_context) ?_
  intro t returned
  exact candidateReturn_of_result h (by intro pass tail eq; cases eq)
    (by intro tail eq; cases eq) t returned

end VG.Proof.Ffdh.Arm.ParameterCandidate
