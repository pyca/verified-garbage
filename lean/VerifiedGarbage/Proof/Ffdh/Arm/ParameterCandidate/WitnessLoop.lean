module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessEnd
public import VerifiedGarbage.Proof.MillerRabin.Arm.Backend
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessStep
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! The complete native witness loop terminates by its remaining entropy bytes. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.MillerRabin.Arm (RoundImpl)

theorem millerRabin_ok (v : RoundImpl) {s : State} {p : WitnessParams} {used passed : Nat}
    (start : WitnessState p used passed s) (more : passed < p.checks) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterCandidate.millerRabin v.name v.code) s (WitnessEnd p used passed s) := by
  let inv := fun k t => ∃ current successes,
    k = p.bytes.length - current + 1 ∧ WitnessState p current successes t ∧ successes < p.checks ∧
    used ≤ current ∧ witnessRemaining p used passed = witnessRemaining p current successes ∧
    Frame (witnessRegions p s.sp) s.mem t.mem ∧ Rest roundClobbers s t
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.millerRabin
  refine WP.loop (M := isa) inv ?_ (p.bytes.length - used + 1) s
    ⟨used, passed, rfl, start, more, Nat.le_refl _, rfl, Frame.refl _ _, Rest.refl _ _⟩
  intro k a state
  obtain ⟨current, successes, measure, ctx, moreNow, consumed, result, changed, rest⟩ := state
  refine WP.mono (witnessStep_ok v ctx moreNow) ?_
  rintro t ⟨nextState, status, zero, delta, restT⟩
  rw [rest.sp] at delta
  have totalFrame := changed.trans delta
  have totalRest := rest.trans restT
  have nextConsumed : used ≤ witnessNextUsed p current := by
    unfold witnessNextUsed
    split <;> omega
  have step := witnessRemaining_step ctx moreNow
  by_cases again : witnessNextStatus p current successes = 4
  · have enough : current + (p.bits + 7) / 8 ≤ p.bytes.length := by
      by_contra short
      simp only [witnessNextStatus, ite_eq_right short] at again
      contradiction
    have drawAgain : drawStatus p successes current = 4 := by
      simpa only [witnessNextStatus, ite_eq_left enough] using again
    have nextMore : witnessNextPassed p current successes < p.checks := by
      rw [witnessNextPassed, ite_eq_left enough]
      exact draw_continue moreNow drawAgain
    rw [ite_eq_left enough, ite_eq_left drawAgain] at step
    have nextResult : witnessRemaining p used passed =
        witnessRemaining p (witnessNextUsed p current) (witnessNextPassed p current successes) := by
      simpa only [witnessNextUsed, witnessNextPassed, ite_eq_left enough] using result.trans step
    right
    refine ⟨?_, p.bytes.length - witnessNextUsed p current + 1, ?_,
      witnessNextUsed p current, witnessNextPassed p current successes, rfl,
      nextState, nextMore, nextConsumed, nextResult, totalFrame, totalRest⟩
    · change some t.z = some true
      rw [zero, decide_eq_true again]
    · rw [witnessNextUsed, ite_eq_left enough]
      have := ctx.bitsPositive
      omega
  · left
    refine ⟨?_, ?_⟩
    · change some t.z = some false
      rw [zero, decide_eq_false again]
    · refine ⟨witnessNextUsed p current, witnessNextPassed p current successes,
        nextState, nextConsumed, ?_, ?_, totalFrame, totalRest⟩
      · by_cases enough : current + (p.bits + 7) / 8 ≤ p.bytes.length
        · have drawStop : drawStatus p successes current ≠ 4 := by
            simpa only [witnessNextStatus, ite_eq_left enough] using again
          rw [ite_eq_left enough, ite_eq_right drawStop] at step
          have final := result.trans step
          rw [final, terminal_draw_status drawStop]
          simpa only [witnessNextStatus, ite_eq_left enough] using status
        · rw [ite_eq_right enough] at step
          rw [result.trans step, witnessResultStatus]
          simpa only [witnessNextStatus, ite_eq_right enough] using status
      · intro pass suffix found
        by_cases enough : current + (p.bits + 7) / 8 ≤ p.bytes.length
        · have drawStop : drawStatus p successes current ≠ 4 := by
            simpa only [witnessNextStatus, ite_eq_left enough] using again
          rw [ite_eq_left enough, ite_eq_right drawStop] at step
          rw [result.trans step] at found
          have suffixEq := congrArg Prod.snd (Option.some.inj found)
          simpa only [witnessNextUsed, ite_eq_left enough] using suffixEq.symm
        · rw [ite_eq_right enough] at step
          rw [result.trans step] at found
          cases found

end VG.Proof.Ffdh.Arm.ParameterCandidate
