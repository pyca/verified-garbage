module

import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateStackUsePrepare
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Candidate
public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateTest
public import VerifiedGarbage.Proof.Framework.X86.Call

/-! # Native candidate generation uses at most 112 bytes below its caller -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.CandidateStackUse
open VG VG.X86 VG.Impl.RsaKeyGen.X86

theorem witness {mont round : Prog isa} (Hm : stackUse mont ≤ 16) (Hr : stackUse round ≤ 56)
    (w : Nat) (montName roundName : String) : stackUse (WitnessStep.code w montName mont roundName round) ≤ 68 := by
  have product := mulY Hm montName 4
  change max 0 (max (max 0 (max 0 (max (max (stackUse (VG.Impl.MillerRabin.X86.mulY montName mont 4)) 0)
    (max 0 (stackUse round + 4 + 8))))) 0) ≤ 68
  omega

theorem millerRabin {mont round : Prog isa} (Hm : stackUse mont ≤ 16) (Hr : stackUse round ≤ 56)
    (w : Nat) (montName roundName : String) : stackUse (MillerRabinLoop.code w montName mont roundName round) ≤ 68 := by
  have bound := witness Hm Hr w montName roundName
  change max 0 (max 0 (max (max 0 (stackUse (WitnessStep.code w montName mont roundName round))) 0)) ≤ 68
  omega

theorem core {mont round : Prog isa} (Hm : stackUse mont ≤ 16) (Hr : stackUse round ≤ 56)
    (w : Nat) (montName roundName : String) : stackUse (CandidateTest.core w montName mont roundName round) ≤ 68 := by
  have setup := prepare Hm w montName
  have witnesses := millerRabin Hm Hr w montName roundName
  change max (stackUse (Prepare.code w montName mont)) (stackUse (MillerRabinLoop.code w montName mont roundName round)) ≤ 68
  omega

theorem test {mont round : Prog isa} (Hm : stackUse mont ≤ 16) (Hr : stackUse round ≤ 56)
    (w : Nat) (montName roundName : String) : stackUse (CandidateTest.code w montName mont roundName round) ≤ 96 := by
  have bound := core Hm Hr w montName roundName
  change max 0 (max 0 (stackUse (CandidateTest.core w montName mont roundName round)) + 28) ≤ 96
  omega

theorem candidateExponent (w : Nat) : stackUse (CandidateExponent.code w) = 20 := rfl

theorem prepareAndTest {mont round : Prog isa} (Hm : stackUse mont ≤ 16) (Hr : stackUse round ≤ 56)
    (w : Nat) (montName roundName : String) : stackUse (Candidate.prepareAndTest w montName mont roundName round) ≤ 96 := by
  have bound := test Hm Hr w montName roundName
  change max (stackUse (CandidateTest.code w montName mont roundName round)) 0 ≤ 96
  omega

theorem exponentCheck {mont round : Prog isa} (Hm : stackUse mont ≤ 16) (Hr : stackUse round ≤ 56)
    (w : Nat) (montName roundName : String) : stackUse (Candidate.exponentCheck w montName mont roundName round) ≤ 96 := by
  have bound := prepareAndTest Hm Hr w montName roundName
  change max (stackUse (CandidateExponent.code w)) (max 0 (max 0 (stackUse (Candidate.prepareAndTest w montName mont roundName round)))) ≤ 96
  rw [candidateExponent]
  omega

theorem sieveCheck {mont round : Prog isa} (Hm : stackUse mont ≤ 16) (Hr : stackUse round ≤ 56)
    (w : Nat) (montName roundName : String) : stackUse (Candidate.sieveCheck w montName mont roundName round) ≤ 96 := by
  have bound := exponentCheck Hm Hr w montName roundName
  have sieve : stackUse (CandidateSieve.code w) = 24 := rfl
  change max (stackUse (CandidateSieve.code w)) (max 0 (max 0 (stackUse (Candidate.exponentCheck w montName mont roundName round)))) ≤ 96
  rw [sieve]
  omega

theorem sized {mont round : Prog isa} (Hm : stackUse mont ≤ 16) (Hr : stackUse round ≤ 56)
    (w : Nat) (montName roundName : String) : stackUse (Candidate.sized w montName mont roundName round) ≤ 96 := by
  have bound := sieveCheck Hm Hr w montName roundName
  change max 0 (max 0 (max 0 (max 0 (stackUse (Candidate.sieveCheck w montName mont roundName round))))) ≤ 96
  omega

theorem dispatch {mont round : Prog isa} (Hm : stackUse mont ≤ 16) (Hr : stackUse round ≤ 56)
    (montName roundName : String) (widths : List Nat) : stackUse (Candidate.dispatch montName mont roundName round widths) ≤ 96 := by
  induction widths with
  | nil => exact Nat.zero_le _
  | cons w rest ih =>
    have bound := sized Hm Hr w montName roundName
    change max 0 (max (stackUse (Candidate.sized w montName mont roundName round))
      (stackUse (Candidate.dispatch montName mont roundName round rest))) ≤ 96
    omega

theorem body {mont round : Prog isa} (Hm : stackUse mont ≤ 16) (Hr : stackUse round ≤ 56)
    (montName roundName : String) : stackUse (Candidate.body montName mont roundName round) ≤ 96 := by
  have bound := dispatch Hm Hr montName roundName Candidate.widths
  change max 0 (max 0 (max 0 (max 0 (max 0 (stackUse (Candidate.dispatch montName mont roundName round Candidate.widths)))))) ≤ 96
  omega

theorem code {mont round : Prog isa} (Hm : stackUse mont ≤ 16) (Hr : stackUse round ≤ 56)
    (montName roundName : String) : stackUse (Candidate.code montName mont roundName round) ≤ 112 := by
  have bound := body Hm Hr montName roundName
  change max (stackUse (Candidate.body montName mont roundName round)) 0 + 16 ≤ 112
  omega

end VG.Proof.RsaKeyGen.X86.CandidateStackUse
