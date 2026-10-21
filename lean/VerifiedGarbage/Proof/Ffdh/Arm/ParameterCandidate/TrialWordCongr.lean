module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialLoopWord
import VerifiedGarbage.Proof.Framework.Omega

/-! The exact reducer result depends only on its public candidate octets and arguments. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm.TrialDivision16

theorem trialWordResult_step (m : Mem) (endPtr divisor inverse : BitVec 32) {n : Nat} (positive : 0 < n)
    (acc : BitVec 32) :
    trialWordResult m endPtr divisor inverse n acc =
      trialWordResult m (endPtr - BitVec.ofNat 32 (min 2 n)) divisor inverse (n - min 2 n)
        (redcWord (trialDigitWord m endPtr n) acc inverse divisor) := by
  rw [trialWordResult, dite_eq_right (by omega)]

theorem trialWordResult_congr {m m' : Mem} {endPtr divisor inverse : BitVec 32} {n : Nat} (acc : BitVec 32)
    (bytes : ∀ i < n, m (State.addr (endPtr - BitVec.ofNat 32 (i + 1))) =
      m' (State.addr (endPtr - BitVec.ofNat 32 (i + 1)))) :
    trialWordResult m endPtr divisor inverse n acc = trialWordResult m' endPtr divisor inverse n acc := by
  induction n using Nat.strongRecOn generalizing endPtr acc with
  | ind n ih =>
    by_cases empty : n = 0
    · subst n
      rw [trialWordResult, dite_eq_left rfl, trialWordResult, dite_eq_left rfl]
    · have positive : 0 < n := by omega
      have low : m (State.addr (endPtr - 1)) = m' (State.addr (endPtr - 1)) := bytes 0 positive
      have digit : trialDigitWord m endPtr n = trialDigitWord m' endPtr n := by
        unfold trialDigitWord
        rw [low]
        by_cases one : n = 1
        · rw [ite_eq_left one, ite_eq_left one]
        · rw [ite_eq_right one, ite_eq_right one]
          have high : m (State.addr (endPtr - 2)) = m' (State.addr (endPtr - 2)) := bytes 1 (by omega)
          rw [high]
      rw [trialWordResult_step m _ _ _ positive acc, trialWordResult_step m' _ _ _ positive acc, digit]
      refine ih _ (by omega) _ ?_
      intro i hi
      rw [BitVec.sub_sub, ← BitVec.ofNat_add]
      have offset : min 2 n + (i + 1) = min 2 n + i + 1 := by omega
      rw [offset]
      exact bytes _ (by omega)

end VG.Proof.Ffdh.Arm.ParameterCandidate
