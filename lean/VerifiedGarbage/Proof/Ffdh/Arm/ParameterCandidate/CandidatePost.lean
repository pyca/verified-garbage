module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateEntered
public import VerifiedGarbage.Spec.Ffdh.Contract
import VerifiedGarbage.Proof.Framework.Omega

/-! Translate native status, output and entropy count to the public FFDH contract. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm

theorem candidatePost_spec {p : CandidateParams} {m : Mem} {r : BitVec 32} (post : candidatePost p m r) :
    let res := Spec.Ffdh.parameterCandidate p.bits p.generator p.bytes
    r.toNat = Spec.Ffdh.candidateStatus res ∧
    Spec.Rsa.bytesAt m (State.addr p.out) p.length =
      (match res with | some (some n, _) => Spec.Rsa.i2osp n p.length | _ => List.replicate p.length 0) ∧
    Spec.Rsa.wordsAt m (State.addr p.usedPtr) 1 =
      [BitVec.ofNat 64 (match res with | some (_, tail) => p.bytes.length - tail.length | none => 0)] := by
  obtain ⟨status, count, bytes⟩ := post
  dsimp only
  rw [← candidateAnswer_spec p]
  cases answer : candidateAnswer p with
  | none =>
    rw [answer] at status count bytes
    exact ⟨by rw [status]; rfl, bytes, count⟩
  | some pair =>
    obtain ⟨pass, tail⟩ := pair
    rw [answer] at status count bytes
    cases pass <;> exact ⟨by rw [status]; rfl, bytes, count⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
