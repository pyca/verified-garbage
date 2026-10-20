module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateParams
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessEnd
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateBuffers
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.Result
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.Finish
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! Candidate returns use the exact tape suffix, encoded p, and API status. -/

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
