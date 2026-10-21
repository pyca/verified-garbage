module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessProgress

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
