module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTWitnessStep
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessStep
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessProgress
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! The native witness loop follows public tape consumption and primality results. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two)
open VG.Proof.MillerRabin.Arm (RoundImpl)

private def nextWitness (p : DrawPoint) : DrawPoint :=
  ⟨p.params, witnessNextUsed p.params p.used, witnessNextPassed p.params p.used p.passed⟩

private structure WitnessIterEnd (p : DrawPoint) (s : State) : Prop where
  state : WitnessState p.params (witnessNextUsed p.params p.used) (witnessNextPassed p.params p.used p.passed) s
  zero : s.z = decide (witnessNextStatus p.params p.used p.passed = 4)

private theorem witnessIterEnd_ok (v : RoundImpl) (p : DrawPoint) (s : State) (h : WitnessLoopStart p s) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterCandidate.witnessStep v.name v.code) s (WitnessIterEnd p) := by
  refine WP.mono (witnessStep_ok v h.1 h.2) ?_
  rintro t ⟨state, _, zero, _, _⟩
  exact ⟨state, zero⟩

private theorem witnessStep_fixed (v : RoundImpl) (p : DrawPoint) :
    RelCT isa (fun s t => WitnessLoopStart p s ∧ WitnessLoopStart p t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.ParameterCandidate.witnessStep v.name v.code)
      (fun s t => WitnessIterEnd p s ∧ WitnessIterEnd p t ∧ s.sp = t.sp) := by
  intro s t trS trT u z h runS runT
  have leak := ((witnessStep_ct v) _ _ _ _ _ _ ⟨p, h⟩ runS runT).1
  obtain ⟨_, _, execS, postS⟩ := witnessIterEnd_ok v p s h.1
  obtain ⟨_, _, execT, postT⟩ := witnessIterEnd_ok v p t h.2.1
  obtain ⟨_, rfl⟩ := Exec.det runS execS
  obtain ⟨_, rfl⟩ := Exec.det runT execT
  exact ⟨leak, postS, postT, (Exec.rdwr runS).2.2.trans (h.2.2.trans (Exec.rdwr runT).2.2.symm)⟩

private def WitnessLoopPair (remaining : Nat) (s t : State) : Prop :=
  ∃ p : DrawPoint, p.params.bytes.length - p.used + 1 = remaining ∧
    WitnessLoopStart p s ∧ WitnessLoopStart p t ∧ s.sp = t.sp

private theorem witnessContinue {p : DrawPoint} {s u : State} (h : WitnessLoopStart p s)
    (post : WitnessIterEnd p u) (go : isa.eval .eq u = some true) :
    WitnessLoopStart (nextWitness p) u ∧
      p.params.bytes.length - (nextWitness p).used + 1 < p.params.bytes.length - p.used + 1 := by
  have again : witnessNextStatus p.params p.used p.passed = 4 := by
    change some u.z = some true at go
    rw [post.zero] at go
    exact of_decide_eq_true (Option.some.inj go)
  have enough : p.used + (p.params.bits + 7) / 8 ≤ p.params.bytes.length := by
    by_contra short
    simp only [witnessNextStatus, ite_eq_right short] at again
    contradiction
  have drawAgain : drawStatus p.params p.passed p.used = 4 := by
    simpa only [witnessNextStatus, ite_eq_left enough] using again
  have nextMore : witnessNextPassed p.params p.used p.passed < p.params.checks := by
    rw [witnessNextPassed, ite_eq_left enough]
    exact draw_continue h.2 drawAgain
  refine ⟨⟨post.state, nextMore⟩, ?_⟩
  change p.params.bytes.length - witnessNextUsed p.params p.used + 1 < _
  rw [witnessNextUsed, ite_eq_left enough]
  have := h.1.bitsPositive
  omega

theorem millerRabin_ct (v : RoundImpl) : RelCT isa (Two WitnessLoopStart)
    (VG.Impl.Ffdh.Arm.ParameterCandidate.millerRabin v.name v.code) (fun _ _ => True) := by
  have step : ∀ n, RelCT isa (WitnessLoopPair n)
      (VG.Impl.Ffdh.Arm.ParameterCandidate.witnessStep v.name v.code)
      (fun u z => isa.eval .eq u = isa.eval .eq z ∧
        (isa.eval .eq u = some false → True) ∧
        (isa.eval .eq u = some true → ∃ m, m < n ∧ WitnessLoopPair m u z)) := by
    intro n s t trS trT u z h runS runT
    obtain ⟨p, remaining, left, right, sp⟩ := h
    obtain ⟨leak, postU, postZ, spUZ⟩ := witnessStep_fixed v p _ _ _ _ _ _ ⟨left, right, sp⟩ runS runT
    refine ⟨leak, ?_, by intro _; trivial, ?_⟩
    · change some u.z = some z.z
      rw [postU.zero, postZ.zero]
    · intro go
      have goZ : isa.eval .eq z = some true := by
        change some z.z = some true
        change some u.z = some true at go
        rw [postZ.zero, ← postU.zero]
        exact go
      have nextU := witnessContinue left postU go
      have nextZ := witnessContinue right postZ goZ
      exact ⟨p.params.bytes.length - (nextWitness p).used + 1,
        by rw [← remaining]; exact nextU.2, nextWitness p, rfl, nextU.1, nextZ.1, spUZ⟩
  intro s t trS trT u z h runS runT
  obtain ⟨p, left, right, sp⟩ := h
  exact RelCT.loop WitnessLoopPair step (p.params.bytes.length - p.used + 1)
    _ _ _ _ _ _ ⟨p, rfl, left, right, sp⟩ runS runT

end VG.Proof.Ffdh.Arm.ParameterCandidate
