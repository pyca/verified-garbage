module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.Draw
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessState
public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Stream
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.WitnessStreamStep
import VerifiedGarbage.Proof.Framework.Omega

/-! Relate a physical witness draw and its native status to the exact shared tape model. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm
open VG.Proof.Ffdh.ParameterCandidate (checkWitnesses checkWitnesses_step)

def witnessRemaining (p : WitnessParams) (used passed : Nat) : Option (Bool × List Byte) :=
  checkWitnesses p.modulus (p.checks - passed) (p.bytes.drop used)

theorem drawStatus_cases (p : WitnessParams) (passed used : Nat) :
    drawStatus p passed used = 1 ∨ drawStatus p passed used = 2 ∨ drawStatus p passed used = 4 := by
  unfold drawStatus
  split
  · unfold roundStatus
    split
    · split <;> simp
    · simp
  · simp

theorem draw_continue {p : WitnessParams} {passed used : Nat} (more : passed < p.checks)
    (status : drawStatus p passed used = 4) : drawPassed p passed used < p.checks := by
  unfold drawPassed drawStatus at *
  by_cases valid : 2 ≤ witnessValue p used ∧ witnessValue p used < p.modulus - 1
  · rw [ite_eq_left valid] at status ⊢
    unfold roundPassed roundStatus at *
    by_cases pass : Spec.Ffdh.mrRound p.modulus (witnessValue p used) = true
    · rw [ite_eq_left pass] at status ⊢
      by_cases done : passed + 1 = p.checks
      · simp only [ite_eq_left done] at status
        contradiction
      · omega
    · rw [ite_eq_right pass] at status ⊢
      contradiction
  · rw [ite_eq_right valid]
    exact more

theorem witnessRemaining_step {s : State} {p : WitnessParams} {used passed : Nat}
    (h : WitnessState p used passed s) (more : passed < p.checks) :
    witnessRemaining p used passed =
      if used + (p.bits + 7) / 8 ≤ p.bytes.length then
        if drawStatus p passed used = 4 then
          witnessRemaining p (used + (p.bits + 7) / 8) (drawPassed p passed used)
        else some (decide (drawStatus p passed used = 1), p.bytes.drop (used + (p.bits + 7) / 8))
      else none := by
  have width : Spec.Ffdh.witnessOctets p.modulus = (p.bits + 7) / 8 := by
    unfold Spec.Ffdh.witnessOctets
    rw [← h.bitsExact]
  have positive : 0 < Spec.Ffdh.witnessOctets p.modulus := by rw [width]; have := h.bitsPositive; omega
  have count : p.checks - passed = (p.checks - passed - 1) + 1 := by omega
  rw [witnessRemaining, count, checkWitnesses_step positive, width, List.length_drop]
  have room : ((p.bits + 7) / 8 ≤ p.bytes.length - used) ↔ used + (p.bits + 7) / 8 ≤ p.bytes.length := by
    have := h.usedBound
    omega
  by_cases enough : used + (p.bits + 7) / 8 ≤ p.bytes.length
  · have available := room.mpr enough
    rw [ite_eq_left available, ite_eq_left enough]
    dsimp only
    rw [← h.bitsExact, List.drop_drop]
    change (if 2 ≤ witnessValue p used ∧ witnessValue p used < p.modulus - 1 then
      if Spec.Ffdh.mrRound p.modulus (witnessValue p used) then
        checkWitnesses p.modulus (p.checks - passed - 1) (p.bytes.drop (used + (p.bits + 7) / 8))
      else some (false, p.bytes.drop (used + (p.bits + 7) / 8))
      else checkWitnesses p.modulus ((p.checks - passed - 1) + 1) (p.bytes.drop (used + (p.bits + 7) / 8))) = _
    by_cases valid : 2 ≤ witnessValue p used ∧ witnessValue p used < p.modulus - 1
    · rw [ite_eq_left valid]
      by_cases pass : Spec.Ffdh.mrRound p.modulus (witnessValue p used) = true
      · rw [ite_eq_left pass]
        by_cases done : passed + 1 = p.checks
        · have exhausted : p.checks - passed - 1 = 0 := by omega
          simp only [exhausted, checkWitnesses, drawStatus, drawPassed, ite_eq_left valid,
            roundStatus, roundPassed, ite_eq_left pass, ite_eq_left done, witnessRemaining,
            show p.checks - (passed + 1) = 0 by omega]
          rfl
        · have remaining : p.checks - (passed + 1) = p.checks - passed - 1 := by omega
          simp only [drawStatus, drawPassed, ite_eq_left valid, roundStatus, roundPassed,
            ite_eq_left pass, ite_eq_right done, witnessRemaining, remaining]
          rfl
      · rw [ite_eq_right pass]
        simp only [drawStatus, ite_eq_left valid, roundStatus, ite_eq_right pass]
        rfl
    · rw [ite_eq_right valid]
      simp only [drawStatus, drawPassed, ite_eq_right valid, witnessRemaining, ← count]
      rfl
  · have short : ¬ (p.bits + 7) / 8 ≤ p.bytes.length - used := fun available => enough (room.mp available)
    rw [ite_eq_right short, ite_eq_right enough]

end VG.Proof.Ffdh.Arm.ParameterCandidate
