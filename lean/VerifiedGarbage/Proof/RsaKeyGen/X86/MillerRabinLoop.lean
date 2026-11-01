module

import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinStep
public import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessChecks
import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinInit
public import VerifiedGarbage.Impl.RsaKeyGen.X86.MillerRabinLoop
public import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinOutcome
public import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessStep

/-! # Complete blinded witness iteration meets the reviewed primality-test result -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.MillerRabinLoop
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.RsaKeyGen
open VG.Impl.RsaKeyGen.X86.MillerRabinLoop

def ranges (g : Geometry) : List (Nat × Nat) := WitnessChecks.ranges ++ WitnessStep.ranges g

theorem loop_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {P : Parameters} (v : P.Valid) {s : State} {k n : Nat} (S : StateAt P k n s) :
    WP isa (.loop (stepAt P.bytes P.words P.g.w montName mont roundName round) .e) s fun t =>
      Prepare.Data P.g P.candidate P.capacity P.p t ∧ Result P t ∧
      WorkspaceFrame P.g (WitnessStep.ranges P.g) s.mem t.mem ∧
      Frame ([⟨P.g.W, P.g.L⟩] ++ [below P.p 108]) s.mem t.mem ∧ Keeps WitnessStep.clob s t := by
  let Inv : Nat → State → Prop := fun q t => ∃ i j, q = j + 1 ∧ StateAt P i j t ∧
    WorkspaceFrame P.g (WitnessStep.ranges P.g) s.mem t.mem ∧
    Frame ([⟨P.g.W, P.g.L⟩] ++ [below P.p 108]) s.mem t.mem ∧ Keeps WitnessStep.clob s t
  have initial : Inv (n + 1) s := ⟨k, n, rfl, S, WorkspaceFrame.refl _ _ _, Frame.refl _ _, Keeps.refl _ _⟩
  refine WP.loop (M := isa) Inv ?_ (n + 1) s initial
  rintro q a ⟨i, j, rfl, A, Wa, Fa, Ka⟩
  refine WP.mono (step_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v A)
    fun t ⟨T, outcome, Wt, Ft, Kt⟩ => ?_
  rcases outcome with ⟨done, _, result⟩ | ⟨again, positive, next⟩
  · exact Or.inl ⟨done, T, result, Wa.trans Wt, Fa.trans Ft, Ka.trans Kt⟩
  · exact Or.inr ⟨again, j, by omega, i + 1, j - 1, by omega, next, Wa.trans Wt, Fa.trans Ft, Ka.trans Kt⟩

theorem code_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {P : Parameters} (v : P.Valid) {s : State}
    (S : Prepare.Data P.g P.candidate P.capacity P.p s)
    (readable : InRegions (s.rd ++ s.wr) (P.rand.setWidth 64) P.randLen)
    (entropy : Spec.Rsa.bytesAt s.mem (P.rand.setWidth 64) P.randLen = P.entropy)
    (randPtr : s.mem.readW (off P.g.W 28) 32 = P.rand)
    (randLength : w32 s.mem P.g.W 32 = P.randLen)
    (used : w32 s.mem P.g.W 152 = P.start) (enough : P.start ≤ P.randLen) :
    WP isa (codeWith P.checks P.bytes P.words P.g.w montName mont roundName round) s fun t =>
      Prepare.Data P.g P.candidate P.capacity P.p t ∧ Result P t ∧
      WorkspaceFrame P.g (ranges P.g) s.mem t.mem ∧
      Frame ([⟨P.g.W, P.g.L⟩] ++ [below P.p 108]) s.mem t.mem ∧ Keeps WitnessStep.clob s t := by
  unfold codeWith
  refine WP.seq (WP.mono (init_ok v S readable entropy randPtr randLength used enough)
    fun a ⟨A, Wa, Fa, Ka⟩ => ?_)
  refine WP.mono (loop_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v A)
    fun t ⟨T, result, Wt, Ft, Kt⟩ => ?_
  have Wsa := Wa.mono (fun r mem => List.mem_append_left _ mem : ∀ r ∈ WitnessChecks.ranges, r ∈ ranges P.g)
  have Wat := Wt.mono (fun r mem => List.mem_append_right _ mem : ∀ r ∈ WitnessStep.ranges P.g, r ∈ ranges P.g)
  exact ⟨T, result, Wsa.trans Wat, (Fa.mono (fun r mem => List.mem_append_left _ mem)).trans Ft,
    (Ka.mono (by unfold WitnessStep.clob; decide)).trans Kt⟩

end VG.Proof.RsaKeyGen.X86.MillerRabinLoop
