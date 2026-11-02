module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinTimingState
public import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinAfterDraw
import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinStep
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # One blinded-loop step has the same trace for equal public entropy offsets -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.MillerRabinLoop
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.RsaKeyGen VG.Proof.Dsa.X86
open VG.Impl.RsaKeyGen.X86.MillerRabinLoop

theorem exhausted_raw : RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (.block exhausted)
    (VG.X86.Taint.Agree (roundTaint [.edi])) := checkedBlockInvariant rfl rfl

theorem again_raw : RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (.block again)
    (VG.X86.Taint.Agree (roundTaint [.edi])) := checkedBlockInvariant rfl rfl

theorem branch_raw {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {P : Parameters} (v : P.Valid) {other : Nat} {entropy : Spec.RsaKeyGen.Rand}
    (w : (P.withSecret other entropy).Valid) (k n : Nat) :
    RelCT isa (AvailablePair P other entropy k n)
      (.ite .b (.block exhausted) (VG.Impl.RsaKeyGen.X86.WitnessStep.codeAt P.bytes P.words P.g.w montName mont roundName round))
      (VG.X86.Taint.Agree (roundTaint [.edi])) := by
  refine VG.RelCT.ite (fun _ _ H => H.2.1.trans H.2.2.symm)
    (exhausted_raw.mono (fun _ _ H => H.1.1.1.2.2) (fun _ _ H => H)) ?_
  intro s t tr ur u z H E G
  have enough : P.start + P.bytes * k + P.bytes ≤ P.randLen := by
    by_contra short
    have bound := H.1.1.2.1.atLoop.used
    rw [v.entropyLength] at bound
    have small : P.randLen - (P.start + P.bytes * k) < P.bytes := by omega
    have condition := H.1.2.1
    rw [H.2, decide_eq_true small] at condition
    cases condition
  have pre : WitnessStep.InitialPair P.g P.capacity P.p P.rand (P.start + P.bytes * k) P.randLen s t P.words :=
    ⟨H.1.1.1, H.1.1.2.1.stepInitial v, H.1.1.2.2.stepInitial w⟩
  obtain ⟨trace, pair⟩ := WitnessStep.codeAt_trace montVerified montNoSp montStack roundVerified roundNoSp roundStack
    v.geometry v.two v.narrow v.wide v.four
    v.length v.randFit v.randLenFit enough v.randSeparate v.low v.stackFar v.lengthFar _ _ _ _ _ _ pre E G
  exact ⟨trace, pair.2.2⟩

theorem step_raw {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {P : Parameters} (v : P.Valid) {other : Nat} {entropy : Spec.RsaKeyGen.Rand}
    (w : (P.withSecret other entropy).Valid) (k n : Nat) :
    RelCT isa (LoopPair P other entropy k n) (stepAt P.bytes P.words P.g.w montName mont roundName round)
      (VG.X86.Taint.Agree (roundTaint [.edi])) := by
  unfold stepAt
  exact RelCT.seq (available_pair v w k n)
    (RelCT.seq (branch_raw montVerified montNoSp montStack roundVerified roundNoSp roundStack v w k n) again_raw)

theorem step_pair {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {P : Parameters} (v : P.Valid) {other : Nat} {entropy : Spec.RsaKeyGen.Rand}
    (w : (P.withSecret other entropy).Valid) (k n : Nat) :
    RelCT isa (LoopPair P other entropy k n) (stepAt P.bytes P.words P.g.w montName mont roundName round)
      (fun s t => Pair P.g [.edi] s t ∧ Outcome P k n s ∧ Outcome (P.withSecret other entropy) k n t) := by
  intro s t tr ur u z H E G
  obtain ⟨trace, agree⟩ := step_raw montVerified montNoSp montStack roundVerified roundNoSp roundStack v w k n _ _ _ _ _ _ H E G
  obtain ⟨U, Ou, _, _, _⟩ := wp_result
    (step_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v H.2.1) E
  obtain ⟨Z, Oz, _, _, _⟩ := wp_result
    (step_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack w H.2.2) G
  exact ⟨trace, ⟨U.ready.context, Z.ready.context, agree⟩, Ou, Oz⟩

end VG.Proof.RsaKeyGen.X86.MillerRabinLoop
