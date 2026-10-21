module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SieveState
public import VerifiedGarbage.Spec.Ffdh
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SieveInit
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SieveStep
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SieveControl
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Sieve
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! The complete 53-prime native sieve implements FFDH's shared primeShape policy. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.X25519.Arm

theorem sieveLoop_ok {s0 s : State} {dst base : BitVec 32} {n value : Nat}
    (start : SieveInv s0 dst base n value 0 s) :
    WP isa (.loop VG.Impl.Ffdh.Arm.ParameterCandidate.sieveStep .ne) s (SieveInv s0 dst base n value 53) := by
  let inv := fun k t => ∃ i, i + k = 53 ∧ 0 < k ∧ SieveInv s0 dst base n value i t
  refine WP.loop (M := isa) inv ?_ 53 s ⟨0, by decide, by decide, start⟩
  intro k t h
  obtain ⟨i, hik, positive, state⟩ := h
  refine WP.mono (sieveStep_ok state (by omega)) ?_
  rintro u ⟨next, flag⟩
  by_cases last : i + 1 = 53
  · left
    refine ⟨?_, last ▸ next⟩
    change some (!u.z) = some false
    simp only [flag, last, decide_true, Bool.not_true]
  · right
    refine ⟨?_, k - 1, by omega, i + 1, by omega, by omega, next⟩
    change some (!u.z) = some true
    simp only [flag, last, decide_false, Bool.not_false]

theorem sieve_ok {s : State} {dst base : BitVec 32} {n : Nat} (h : SieveContext dst base n s) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.sieve s fun t =>
      SieveContext dst base n t ∧
      t.z = !(sieveAny (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n)) 53) ∧
      Frame [sieveLocal s.sp] s.mem t.mem ∧ Rest sieveRegs s t := by
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.sieve VG.Impl.Ffdh.Arm.ParameterCandidate.seqs
  refine WP.seq (WP.mono (sieveInit_ok h) ?_)
  intro u start
  refine WP.seq (WP.mono (sieveLoop_ok start) ?_)
  intro v state
  refine WP.seq (WP.mono (sieveFinish_ok state.context.read.frame.space state.bad) ?_)
  rintro t ⟨⟨flag, memory⟩, rest⟩
  refine WP.block_nil ⟨state.context.after_memory memory rest, flag, ?_,
    state.rest.trans (rest.mono (by simp [sieveRegs]))⟩
  rw [memory]
  exact state.changed

theorem sieve_shape_ok {s : State} {dst base : BitVec 32} {n : Nat} (h : SieveContext dst base n s)
    (large : 8161 < Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n))
    (odd : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n) % 2 = 1) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.sieve s fun t =>
      SieveContext dst base n t ∧
      t.z = Spec.Ffdh.primeShape (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n)) ∧
      Frame [sieveLocal s.sp] s.mem t.mem ∧ Rest sieveRegs s t := by
  refine WP.mono (sieve_ok h) ?_
  rintro t ⟨context, flag, changed, rest⟩
  rw [VG.Proof.Ffdh.ParameterCandidate.primeShape_sieve large odd]
  exact ⟨context, flag, changed, rest⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
