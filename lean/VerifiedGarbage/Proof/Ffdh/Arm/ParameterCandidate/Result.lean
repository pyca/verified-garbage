module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ResultContext
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.Finish
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.Status
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! Interpret the native phase status as the candidate API's output and count. -/

@[expose] public section
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
