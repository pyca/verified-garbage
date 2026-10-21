module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialStepWord
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialValue
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! Exact accumulator propagation through every native small-prime digit. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.X25519.Arm VG.Proof.Bignum.Arm.TrialDivision16

def trialWordResult (m : Mem) (endPtr divisor inverse : BitVec 32) (n : Nat) (acc : BitVec 32) : BitVec 32 :=
  if _empty : n = 0 then acc else
    trialWordResult m (endPtr - BitVec.ofNat 32 (min 2 n)) divisor inverse (n - min 2 n)
      (redcWord (trialDigitWord m endPtr n) acc inverse divisor)
termination_by n
decreasing_by omega

theorem trialLoopWord_ok (s : State) {n : Nat} (positive : 0 < n) (fits : n < 2 ^ 32)
    (count : s.gpr .r1 = BitVec.ofNat 32 n) (readable : TrialReadable s (s.gpr .r0) n) :
    WP isa (.loop VG.Impl.Ffdh.Arm.ParameterCandidate.trialStep .ne) s fun t =>
      t.gpr .r2 = trialWordResult s.mem (s.gpr .r0) (s.gpr .r3) (s.gpr .r4) n (s.gpr .r2) ∧
      t.mem = s.mem ∧ Rest [.r0, .r1, .r2, .r5, .r6, .r7] s t := by
  induction n using Nat.strongRecOn generalizing s with
  | ind n ih =>
    obtain ⟨tr, u, run, value, ptr, cnt, flag, memory, rest⟩ :=
      trialStepWord_ok s positive fits count (readable.low positive) (fun h => readable.high h)
    have recurrence : trialWordResult s.mem (s.gpr .r0) (s.gpr .r3) (s.gpr .r4) n (s.gpr .r2) =
        trialWordResult u.mem (u.gpr .r0) (u.gpr .r3) (u.gpr .r4) (n - min 2 n) (u.gpr .r2) := by
      rw [trialWordResult, dite_eq_right (by omega)]
      rw [memory, ptr, value, rest.gpr .r3 (by simp), rest.gpr .r4 (by simp)]
    by_cases last : n ≤ 2
    · have zero : n - min 2 n = 0 := by omega
      have result : u.gpr .r2 = trialWordResult s.mem (s.gpr .r0) (s.gpr .r3) (s.gpr .r4) n (s.gpr .r2) := by
        rw [recurrence, zero, trialWordResult, dite_eq_left rfl]
      exact ⟨_, u, .loopExit run (by change some (!u.z) = some false; rw [flag, decide_eq_true last]; rfl), result, memory, rest⟩
    · have smaller : n - min 2 n < n := by omega
      have readU : TrialReadable u (u.gpr .r0) (n - min 2 n) := by
        rw [ptr]
        exact readable.advance rest (Nat.min_le_right 2 n)
      obtain ⟨trT, t, runT, resultT, memoryT, restT⟩ := ih _ smaller u (by omega) (by omega) cnt readU
      exact ⟨_, t, .loopNext run (by change some (!u.z) = some true; rw [flag, decide_eq_false last]; rfl) runT,
        resultT.trans recurrence.symm, memoryT.trans memory, rest.trans restT⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
