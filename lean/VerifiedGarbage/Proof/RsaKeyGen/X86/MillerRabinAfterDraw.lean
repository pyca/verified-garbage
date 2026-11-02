module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.MillerRabinLoop
public import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinOutcome
public import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessStep

import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinControl
import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinPreserve
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedDataGap
import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinState
import VerifiedGarbage.Proof.RsaKeyGen.MrCounts
/-! # A passing witness continues or accepts; a failing witness rejects -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/MillerRabinDraw.lean`, which only this module imported.
section

/-! # A native witness draw advances the reviewed loop's exact counters and status -/

section
namespace VG.Proof.RsaKeyGen.X86.MillerRabinLoop
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.RsaKeyGen

theorem draw_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {P : Parameters} (v : P.Valid) {s : State} {k n : Nat} (S : StateAt P k n s)
    (enough : P.start + P.bytes * k + P.bytes ≤ P.randLen) :
    WP isa (VG.Impl.RsaKeyGen.X86.WitnessStep.codeAt P.bytes P.words P.g.w montName mont roundName round) s fun t =>
      Prepare.Data P.g P.candidate P.capacity P.p t ∧
      w32 t.mem P.g.W 152 = P.start + P.bytes * k + P.bytes ∧ w32 t.mem P.g.W 176 = k + 1 ∧
      w32 t.mem P.g.W 192 = (mrSB P.candidate P.bytes P.start P.entropy (k + 1)).2 ∧
      w32 t.mem P.g.W 168 =
        (if Spec.RsaKeyGen.mrIteration P.candidate P.twos.1 P.twos.2
            (wit P.candidate P.bytes P.entropy (P.start + P.bytes * k)).1 then
          if goS P.checks (mrSB P.candidate P.bytes P.start P.entropy (k + 1)) then 4 else 1
        else 3) ∧
      WorkspaceFrame P.g (WitnessStep.ranges P.g) s.mem t.mem ∧
      Frame ([⟨P.g.W, P.g.L⟩] ++ [below P.p 108]) s.mem t.mem ∧ Keeps WitnessStep.clob s t := by
  have counts := S.countFit v
  refine WP.mono (WitnessStep.codeAt_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v.geometry
    v.two v.narrow v.wide v.four
    v.length S.prepared S.randPtr S.used v.randFit v.randLenFit enough S.readable v.randSeparate v.odd (by have := v.large; omega)
    v.shape counts.1 counts.2 v.low v.stackFar v.lengthFar) fun t ⟨T, used, rounds, uniform, status, W, F, K⟩ => ?_
  rw [S.rounds] at rounds
  rw [S.sample enough, S.uniform, ← mrSB_uniform_next] at uniform
  rw [S.sample enough, S.rounds, S.uniform, S.checks, count_policy] at status
  exact ⟨T, used, rounds, uniform, status, W, F, K⟩

end VG.Proof.RsaKeyGen.X86.MillerRabinLoop
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.MillerRabinLoop
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.RsaKeyGen
open VG.Impl.RsaKeyGen.X86.MillerRabinLoop

def Outcome (P : Parameters) (k n : Nat) (t : State) : Prop :=
  (isa.eval .e t = some false ∧ n = 0 ∧ Result P t) ∨
    (isa.eval .e t = some true ∧ 0 < n ∧ StateAt P (k + 1) (n - 1) t)

theorem draw_again_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {P : Parameters} (v : P.Valid) {s : State} {k n : Nat} (S : StateAt P k n s)
    (enough : P.start + P.bytes * k + P.bytes ≤ P.randLen) :
    WP isa (.seq (VG.Impl.RsaKeyGen.X86.WitnessStep.codeAt P.bytes P.words P.g.w montName mont roundName round) (.block again)) s fun t =>
      Prepare.Data P.g P.candidate P.capacity P.p t ∧ Outcome P k n t ∧
      WorkspaceFrame P.g (WitnessStep.ranges P.g) s.mem t.mem ∧
      Frame ([⟨P.g.W, P.g.L⟩] ++ [below P.p 108]) s.mem t.mem ∧ Keeps WitnessStep.clob s t := by
  refine WP.seq (WP.mono (draw_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v S enough)
    fun a ⟨A, usedA, roundsA, uniformA, statusA, Wa, Fa, Ka⟩ => ?_)
  refine WP.mono (again_ok v.geometry A.ready.scratch) fun t ⟨Z, mem, Kt⟩ => ?_
  have T := A.keepHeader v.geometry (d := 128) (bytes := 0) (by decide) (by decide)
    (show Outside P.g.W 128 0 a.mem t.mem from by rw [mem]; exact Outside.refl _ _ _ _) Kt (by decide) (by decide)
  have W : WorkspaceFrame P.g (WitnessStep.ranges P.g) s.mem t.mem := by rw [mem]; exact Wa
  have F : Frame ([⟨P.g.W, P.g.L⟩] ++ [below P.p 108]) s.mem t.mem := by rw [mem]; exact Fa
  refine ⟨T, ?_, W, F, Ka.widen Kt⟩
  have ev : isa.eval .e t = some (decide (w32 a.mem P.g.W 168 = 4)) := Z
  cases passed : Spec.RsaKeyGen.mrIteration P.candidate P.twos.1 P.twos.2
      (wit P.candidate P.bytes P.entropy (P.start + P.bytes * k)).1 with
  | false =>
    have failed := S.failed v enough passed
    simp only [passed] at statusA
    refine Or.inl ⟨?_, failed.1, ?_⟩
    · rw [ev, statusA]; rfl
    · unfold Result
      rw [failed.2, mem]
      refine ⟨statusA, ?_⟩
      rw [usedA, List.length_drop]
      have bound := enough
      rw [← v.entropyLength] at bound
      omega
  | true =>
    by_cases more : goS P.checks (mrSB P.candidate P.bytes P.start P.entropy (k + 1))
    · have next := mrLoopAt_next S.atLoop v.witnessBytes
        (by have := v.narrow; have := v.two; omega)
        (by rw [v.entropyLength]; exact enough) passed more
      simp only [passed, ↓reduceIte, more] at statusA
      have nextState := StateAt.next v S A usedA roundsA uniformA next.2 Wa Fa Ka
      refine Or.inr ⟨?_, next.1, nextState.keepMem v mem Kt (by decide) (by decide)⟩
      rw [ev, statusA]; rfl
    · have done := S.accepted v enough passed more
      simp only [passed, ↓reduceIte, more] at statusA
      refine Or.inl ⟨?_, done.1, ?_⟩
      · rw [ev, statusA]; rfl
      · unfold Result
        rw [done.2, mem]
        refine ⟨statusA, ?_⟩
        rw [usedA, List.length_drop]
        have bound := enough
        rw [← v.entropyLength] at bound
        omega

end VG.Proof.RsaKeyGen.X86.MillerRabinLoop
