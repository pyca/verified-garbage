module

import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinDraw
public import VerifiedGarbage.Impl.RsaKeyGen.X86.MillerRabinLoop
import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinControl
import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinPreserve
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedDataGap
public import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinOutcome
public import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessStep

/-! # A passing witness continues or accepts; a failing witness rejects -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.MillerRabinLoop
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.RsaKeyGen
open VG.Impl.RsaKeyGen.X86.MillerRabinLoop

def Outcome (P : Parameters) (k n : Nat) (t : State) : Prop :=
  (isa.eval .e t = some false ∧ n = 0 ∧ Result P t) ∨
    (isa.eval .e t = some true ∧ 0 < n ∧ StateAt P (k + 1) (n - 1) t)

theorem draw_again_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Spec.Rsa.Mont.mulContract abi 16))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 16)
    (roundVerified : Verified target round (Spec.MillerRabin.roundContract abi Spec.MillerRabin.compact 56))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 56)
    {P : Parameters} (v : P.Valid) {s : State} {k n : Nat} (S : StateAt P k n s)
    (enough : P.bytes * (k + 1) + P.bytes ≤ P.randLen) :
    WP isa (.seq (VG.Impl.RsaKeyGen.X86.WitnessStep.code P.g.w montName mont roundName round) (.block again)) s fun t =>
      Prepare.Data P.g P.candidate P.capacity P.p t ∧ Outcome P k n t ∧
      WorkspaceFrame P.g (WitnessStep.ranges P.g) s.mem t.mem ∧
      Frame ([⟨P.g.W, P.g.L⟩] ++ [below P.p 68]) s.mem t.mem ∧ Keeps WitnessStep.clob s t := by
  refine WP.seq (WP.mono (draw_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v S enough)
    fun a ⟨A, usedA, roundsA, uniformA, statusA, Wa, Fa, Ka⟩ => ?_)
  refine WP.mono (again_ok v.geometry A.ready.scratch) fun t ⟨Z, mem, Kt⟩ => ?_
  have T := A.keepHeader v.geometry (d := 128) (bytes := 0) (by decide) (by decide)
    (show Outside P.g.W 128 0 a.mem t.mem from by rw [mem]; exact Outside.refl _ _ _ _) Kt (by decide) (by decide)
  have W : WorkspaceFrame P.g (WitnessStep.ranges P.g) s.mem t.mem := by rw [mem]; exact Wa
  have F : Frame ([⟨P.g.W, P.g.L⟩] ++ [below P.p 68]) s.mem t.mem := by rw [mem]; exact Fa
  refine ⟨T, ?_, W, F, Ka.widen Kt⟩
  have ev : isa.eval .e t = some (decide (w32 a.mem P.g.W 168 = 4)) := Z
  cases passed : Spec.RsaKeyGen.mrIteration P.candidate P.twos.1 P.twos.2
      (wit P.candidate P.bytes P.entropy (P.bytes * (k + 1))).1 with
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
    by_cases more : goS P.checks (mrS P.candidate P.bytes P.entropy (k + 1))
    · have next := mrAt_next S.atLoop v.witnessBytes
        (by have := v.geometry.minWidth; unfold Parameters.bytes; omega)
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
