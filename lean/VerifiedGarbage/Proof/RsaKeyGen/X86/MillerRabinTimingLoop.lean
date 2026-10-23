module

import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinTimingStep
public import VerifiedGarbage.Impl.RsaKeyGen.X86.MillerRabinLoop
public import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinTimingState

/-! # Equal specified witness counts give equal traces across the complete blinded loop -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.MillerRabinLoop
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.RsaKeyGen
open VG.Impl.RsaKeyGen.X86.MillerRabinLoop

theorem loop_trace {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Spec.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Spec.MillerRabin.roundContract abi Spec.MillerRabin.compact 96))
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
