module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PhaseInput
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PhaseFrame
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessEnd
public import VerifiedGarbage.Proof.MillerRabin.Arm.Backend
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PreparedWitness
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessLoop
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! One complete native probable-prime phase: prepare, sample, and run shared rounds. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.MillerRabin.Arm (RoundImpl)

def PhaseEnd (p : WitnessParams) (used : Nat) (s t : State) : Prop :=
  ∃ nextUsed nextPassed, WitnessState p nextUsed nextPassed t ∧ used ≤ nextUsed ∧
    t.gpr .r3 = BitVec.ofNat 32 (witnessResultStatus (witnessRemaining p used 0)) ∧
    (∀ pass rest, witnessRemaining p used 0 = some (pass, rest) → rest = p.bytes.drop nextUsed) ∧
    Frame (phaseRegions p s.sp) s.mem t.mem ∧ Rest roundClobbers s t

theorem phaseRun_ok (v : RoundImpl) {s : State} {p : WitnessParams} {src : BitVec 32} {k used : Nat}
    (h : PhaseInput p src k used s) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterCandidate.phaseRun v.name v.code) s (PhaseEnd p used s) := by
  rw [VG.Impl.Ffdh.Arm.ParameterCandidate.phaseRun, WP.seq_iff]
  refine WP.mono (preparedWitness_ok h) ?_
  rintro u ⟨state, changed, rest⟩
  refine WP.mono (millerRabin_ok v state h.checksPositive) ?_
  rintro t ⟨nextUsed, nextPassed, stateT, consumed, status, suffix, changedT, restT⟩
  have phaseFrame := phase_witness_frame state.saved.space changedT
  rw [rest.sp] at phaseFrame
  exact ⟨nextUsed, nextPassed, stateT, consumed, status, suffix,
    (phase_preparation_frame h.saved.space changed).trans phaseFrame, rest.trans restT⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
