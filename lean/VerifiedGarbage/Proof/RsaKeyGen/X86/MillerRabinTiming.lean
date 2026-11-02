module

public import VerifiedGarbage.Proof.RsaKeyGen.CandLeak
public import VerifiedGarbage.Impl.RsaKeyGen.X86.MillerRabinLoop
public import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinTimingState

import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinInit
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinTimingStep
import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessChecks
import VerifiedGarbage.Proof.MillerRabin.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.KernelRfl
/-! # The complete prepared primality loop reveals only its consumed entropy length -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/MillerRabinTimingLoop.lean`, which only this module imported.
section

/-! # Equal specified witness counts give equal traces across the complete blinded loop -/

section
namespace VG.Proof.RsaKeyGen.X86.MillerRabinLoop
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.RsaKeyGen
open VG.Impl.RsaKeyGen.X86.MillerRabinLoop

theorem loop_trace {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {P : Parameters} (v : P.Valid) {other : Nat} {entropy : Spec.RsaKeyGen.Rand}
    (w : (P.withSecret other entropy).Valid) (k n : Nat) :
    RelCT isa (LoopPair P other entropy k n) (.loop (stepAt P.bytes P.words P.g.w montName mont roundName round) .e) (Pair P.g [.edi]) := by
  let Inv : Nat → State → State → Prop := fun q s t => ∃ k n, q = n + 1 ∧ LoopPair P other entropy k n s t
  have run : RelCT isa (Inv (n + 1)) (.loop (stepAt P.bytes P.words P.g.w montName mont roundName round) .e) (Pair P.g [.edi]) := by
    refine RelCT.loop (M := isa) Inv ?_ (n + 1)
    rintro q s t tr ur u z ⟨i, j, rfl, H⟩ E G
    obtain ⟨trace, pair, Ou, Oz⟩ := step_pair montVerified montNoSp montStack roundVerified roundNoSp roundStack v w i j _ _ _ _ _ _ H E G
    rcases Ou with ⟨Eu, zeroU, _⟩ | ⟨Eu, positiveU, U⟩ <;>
      rcases Oz with ⟨Ez, zeroZ, _⟩ | ⟨Ez, positiveZ, Z⟩
    · refine ⟨trace, Eu.trans Ez.symm, fun _ => pair, ?_⟩
      intro continuing
      rw [Eu] at continuing
      cases continuing
    · omega
    · omega
    · refine ⟨trace, Eu.trans Ez.symm, ?_, ?_⟩
      · intro done
        rw [Eu] at done
        cases done
      · intro _
        exact ⟨j, by omega, i + 1, j - 1, by omega, pair, U, Z⟩
  exact run.mono (fun _ _ H => ⟨k, n, rfl, H⟩) (fun _ _ H => H)

end VG.Proof.RsaKeyGen.X86.MillerRabinLoop
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/WitnessChecksTiming.lean`, which only this module imported.
section

/-! # Initializing the witness policy has a width-only trace -/

section
namespace VG.Proof.RsaKeyGen.X86.WitnessChecks
open VG VG.X86 VG.Proof.MillerRabin.X86 VG.Proof.Dsa.X86

theorem codeOf_trace (checks : Nat) : RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi]))
    (.block (VG.Impl.RsaKeyGen.X86.WitnessChecks.codeOf checks)) (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  erased_relCT _ (.block (VG.Impl.RsaKeyGen.X86.WitnessChecks.codeOf 0)) (.block []) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)

theorem code_trace (w : Nat) : RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi]))
    (.block (VG.Impl.RsaKeyGen.X86.WitnessChecks.code w)) (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  codeOf_trace _

end VG.Proof.RsaKeyGen.X86.WitnessChecks
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.MillerRabinLoop
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.RsaKeyGen VG.Proof.Dsa.X86
open VG.Impl.RsaKeyGen.X86.MillerRabinLoop

def Parameters.iterations (P : Parameters) : Nat :=
  itersOf P.bytes P.entropy.length (shapeOf P.test) P.start - 1

def Initial (P : Parameters) (s : State) : Prop :=
  Prepare.Data P.g P.candidate P.capacity P.p s ∧
    InRegions (s.rd ++ s.wr) (P.rand.setWidth 64) P.randLen ∧
    Spec.Rsa.bytesAt s.mem (P.rand.setWidth 64) P.randLen = P.entropy ∧
    s.mem.readW (off P.g.W 28) 32 = P.rand ∧ w32 s.mem P.g.W 32 = P.randLen ∧
    w32 s.mem P.g.W 152 = P.start

def InitialPair (P : Parameters) (other : Nat) (entropy : Spec.RsaKeyGen.Rand) (s t : State) : Prop :=
  Pair P.g [.edi] s t ∧ Initial P s ∧ Initial (P.withSecret other entropy) t ∧
    P.iterations = (P.withSecret other entropy).iterations

theorem init_pair {P : Parameters} (v : P.Valid) {other : Nat} {entropy : Spec.RsaKeyGen.Rand}
    (w : (P.withSecret other entropy).Valid) (enough : P.start ≤ P.randLen) :
    RelCT isa (InitialPair P other entropy) (.block (VG.Impl.RsaKeyGen.X86.WitnessChecks.codeOf P.checks))
      (LoopPair P other entropy 0 P.iterations) := by
  intro s t tr ur u z H E G
  obtain ⟨trace, agree⟩ := WitnessChecks.codeOf_trace P.checks _ _ _ _ _ _ H.1.2.2 E G
  obtain ⟨S, readS, bytesS, ptrS, lenS, usedS⟩ := H.2.1
  obtain ⟨T, readT, bytesT, ptrT, lenT, usedT⟩ := H.2.2.1
  obtain ⟨U, _, _, _⟩ := wp_result (init_ok v S readS bytesS ptrS lenS usedS enough) E
  obtain ⟨Z, _, _, _⟩ := wp_result (init_ok w T readT bytesT ptrT lenT usedT enough) G
  have iters := H.2.2.2
  change P.iterations = (P.withSecret other entropy).iterations at iters
  change StateAt (P.withSecret other entropy) 0 (P.withSecret other entropy).iterations z at Z
  rw [← iters] at Z
  exact ⟨trace, ⟨U.prepared.ready.context, Z.prepared.ready.context, agree⟩, U, Z⟩

theorem code_trace {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {P : Parameters} (v : P.Valid) {other : Nat} {entropy : Spec.RsaKeyGen.Rand}
    (w : (P.withSecret other entropy).Valid) (enough : P.start ≤ P.randLen) :
    RelCT isa (InitialPair P other entropy) (codeWith P.checks P.bytes P.words P.g.w montName mont roundName round) (Pair P.g [.edi]) := by
  unfold codeWith
  exact RelCT.seq (init_pair v w enough)
    (loop_trace montVerified montNoSp montStack roundVerified roundNoSp roundStack v w 0 P.iterations)

end VG.Proof.RsaKeyGen.X86.MillerRabinLoop
