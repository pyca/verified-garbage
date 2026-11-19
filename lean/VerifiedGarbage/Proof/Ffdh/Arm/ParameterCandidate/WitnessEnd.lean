module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.Draw
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessState
public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Stream
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.WitnessStreamStep
import VerifiedGarbage.Proof.Framework.Omega

/-! ### `Ffdh.Arm.ParameterCandidate.WitnessProgress`, which this module and modules that import it used -/

section

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
      · omega_using [more, done]
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
  have positive : 0 < Spec.Ffdh.witnessOctets p.modulus := by rw [width]; have := h.bitsPositive; omega_using [this]
  have count : p.checks - passed = (p.checks - passed - 1) + 1 := by omega_using [more]
  rw [witnessRemaining, count, checkWitnesses_step positive, width, List.length_drop]
  have room : ((p.bits + 7) / 8 ≤ p.bytes.length - used) ↔ used + (p.bits + 7) / 8 ≤ p.bytes.length := by
    have := h.usedBound
    omega_using [this]
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
        · have exhausted : p.checks - passed - 1 = 0 := by omega_using [done]
          simp only [exhausted, checkWitnesses, drawStatus, drawPassed, ite_eq_left valid,
            roundStatus, roundPassed, ite_eq_left pass, ite_eq_left done, witnessRemaining,
            show p.checks - (passed + 1) = 0 by omega_using [done]]
          rfl
        · have remaining : p.checks - (passed + 1) = p.checks - passed - 1 := by omega_using []
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

end

end

/-! A phase returns the shared tape model's status and exact remaining suffix. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.X25519.Arm

def witnessResultStatus : Option (Bool × List Byte) → Nat
  | none => 0
  | some (true, _) => 1
  | some (false, _) => 2

def WitnessEnd (p : WitnessParams) (used passed : Nat) (s t : State) : Prop :=
  ∃ nextUsed nextPassed, WitnessState p nextUsed nextPassed t ∧ used ≤ nextUsed ∧
    t.gpr .r3 = BitVec.ofNat 32 (witnessResultStatus (witnessRemaining p used passed)) ∧
    (∀ pass rest, witnessRemaining p used passed = some (pass, rest) → rest = p.bytes.drop nextUsed) ∧
    Frame (witnessRegions p s.sp) s.mem t.mem ∧ Rest roundClobbers s t

theorem terminal_draw_status {p : WitnessParams} {used passed : Nat} (stop : drawStatus p passed used ≠ 4)
    (rest : List Byte) :
    witnessResultStatus (some (decide (drawStatus p passed used = 1), rest)) = drawStatus p passed used := by
  rcases drawStatus_cases p passed used with status | status | status
  · rw [status]
    rfl
  · rw [status]
    rfl
  · exact False.elim (stop status)

end VG.Proof.Ffdh.Arm.ParameterCandidate
