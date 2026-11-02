module

import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinExhausted
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessAvailable
public import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinAfterDraw

/-! # A complete blinded-loop step either stops or decreases its specified iteration count -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.MillerRabinLoop
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.RsaKeyGen
open VG.Impl.RsaKeyGen.X86.MillerRabinLoop

theorem step_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {P : Parameters} (v : P.Valid) {s : State} {k n : Nat} (S : StateAt P k n s) :
    WP isa (stepAt P.bytes P.words P.g.w montName mont roundName round) s fun t =>
      Prepare.Data P.g P.candidate P.capacity P.p t ∧ Outcome P k n t ∧
      WorkspaceFrame P.g (WitnessStep.ranges P.g) s.mem t.mem ∧
      Frame ([⟨P.g.W, P.g.L⟩] ++ [below P.p 108]) s.mem t.mem ∧ Keeps WitnessStep.clob s t := by
  have usedBound : P.start + P.bytes * k ≤ P.randLen := by
    have := S.atLoop.used
    rw [v.entropyLength] at this
    exact this
  unfold stepAt
  refine WP.seq (WP.mono (WitnessAvailable.codeAt_ok S.prepared.ready.scratch v.geometry.headerFit
    (by have := v.geometry.maxWidth; have := v.wide; omega) S.randLength S.used usedBound) fun a ⟨CF, mem, Ka⟩ => ?_)
  have A := S.keepMem v mem Ka (by decide) (by decide)
  have condition : isa.eval .b a = some (decide (¬ P.start + P.bytes * k + P.bytes ≤ P.randLen)) := by
    change a.cf = _
    rw [CF]
    congr 1
    apply decide_eq_decide.mpr
    change (P.randLen - (P.start + P.bytes * k) < P.bytes) ↔ ¬ P.start + P.bytes * k + P.bytes ≤ P.randLen
    omega
  refine WP.seq ?_
  by_cases enough : P.start + P.bytes * k + P.bytes ≤ P.randLen
  · refine WP.ite false (by rw [condition]; simp only [enough, not_true_eq_false, decide_false])
      (fun impossible => nomatch impossible) (fun _ => ?_)
    apply WP.seq_iff.mp
    refine WP.mono (draw_again_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v A enough)
      fun t ⟨T, outcome, W, F, Kt⟩ => ?_
    rw [mem] at W F
    exact ⟨T, outcome, W, F, (Ka.mono (by unfold WitnessStep.clob; decide)).trans Kt⟩
  · refine WP.ite true (by rw [condition]; simp only [enough, not_false_eq_true, decide_true])
      (fun _ => ?_) (fun impossible => nomatch impossible)
    apply WP.seq_iff.mp
    refine WP.mono (exhausted_again_ok v A enough) fun t ⟨T, outcome, W, F, Kt⟩ => ?_
    rw [mem] at W F
    exact ⟨T, outcome, W, F, (Ka.mono (by unfold WitnessStep.clob; decide)).trans Kt⟩

end VG.Proof.RsaKeyGen.X86.MillerRabinLoop
