module

import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateStackUsePrepare
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Candidate
public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateTest
public import VerifiedGarbage.Proof.Framework.X86.Call

/-! # Native candidate generation uses at most 152 bytes below its caller -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.CandidateStackUse
open VG VG.X86 VG.Impl.RsaKeyGen.X86

theorem witnessAt {mont round : Prog isa} (Hm : stackUse mont ≤ 56) (Hr : stackUse round ≤ 96)
    (D k w : Nat) (montName roundName : String) :
    stackUse (WitnessStep.codeAt D k w montName mont roundName round) ≤ 108 := by
  have product := mulY Hm montName 4
  change max 0 (max (max (max 0 (max 0 0)) (max 0 (max (max (stackUse (VG.Impl.MillerRabin.X86.mulY montName mont 4)) 0)
    (max 0 (stackUse round + 4 + 8))))) 0) ≤ 108
  omega

theorem witness {mont round : Prog isa} (Hm : stackUse mont ≤ 56) (Hr : stackUse round ≤ 96)
    (w : Nat) (montName roundName : String) : stackUse (WitnessStep.code w montName mont roundName round) ≤ 108 :=
  witnessAt Hm Hr _ _ w montName roundName

theorem millerRabinWith {mont round : Prog isa} (Hm : stackUse mont ≤ 56) (Hr : stackUse round ≤ 96)
    (checks D k w : Nat) (montName roundName : String) :
    stackUse (MillerRabinLoop.codeWith checks D k w montName mont roundName round) ≤ 108 := by
  have bound := witnessAt Hm Hr D k w montName roundName
  change max 0 (max 0 (max (max 0 (stackUse (WitnessStep.codeAt D k w montName mont roundName round))) 0)) ≤ 108
  omega

theorem millerRabinOf {mont round : Prog isa} (Hm : stackUse mont ≤ 56) (Hr : stackUse round ≤ 96)
    (checks w : Nat) (montName roundName : String) :
    stackUse (MillerRabinLoop.codeOf checks w montName mont roundName round) ≤ 108 :=
  millerRabinWith Hm Hr checks _ _ w montName roundName

theorem millerRabin {mont round : Prog isa} (Hm : stackUse mont ≤ 56) (Hr : stackUse round ≤ 96)
    (w : Nat) (montName roundName : String) : stackUse (MillerRabinLoop.code w montName mont roundName round) ≤ 108 :=
  millerRabinOf Hm Hr _ w montName roundName

theorem coreWith {mont round : Prog isa} (Hm : stackUse mont ≤ 56) (Hr : stackUse round ≤ 96)
    (e checks D k w : Nat) (montName roundName : String) :
    stackUse (CandidateTest.coreWith e checks D k w montName mont roundName round) ≤ 108 := by
  have setup := prepareAt Hm e w montName
  have witnesses := millerRabinWith Hm Hr checks D k w montName roundName
  change max (stackUse (Prepare.codeAt e w montName mont))
    (stackUse (MillerRabinLoop.codeWith checks D k w montName mont roundName round)) ≤ 108
  omega

theorem coreOf {mont round : Prog isa} (Hm : stackUse mont ≤ 56) (Hr : stackUse round ≤ 96)
    (checks w : Nat) (montName roundName : String) :
    stackUse (CandidateTest.coreOf checks w montName mont roundName round) ≤ 108 :=
  coreWith Hm Hr _ checks _ _ w montName roundName

theorem core {mont round : Prog isa} (Hm : stackUse mont ≤ 56) (Hr : stackUse round ≤ 96)
    (w : Nat) (montName roundName : String) : stackUse (CandidateTest.core w montName mont roundName round) ≤ 108 :=
  coreOf Hm Hr _ w montName roundName

theorem testWith {mont round : Prog isa} (Hm : stackUse mont ≤ 56) (Hr : stackUse round ≤ 96)
    (e checks D k w : Nat) (montName roundName : String) :
    stackUse (CandidateTest.codeWith e checks D k w montName mont roundName round) ≤ 136 := by
  have bound := coreWith Hm Hr e checks D k w montName roundName
  change max 0 (max 0 (stackUse (CandidateTest.coreWith e checks D k w montName mont roundName round)) + 28) ≤ 136
  omega

theorem testOf {mont round : Prog isa} (Hm : stackUse mont ≤ 56) (Hr : stackUse round ≤ 96)
    (checks w : Nat) (montName roundName : String) :
    stackUse (CandidateTest.codeOf checks w montName mont roundName round) ≤ 136 :=
  testWith Hm Hr _ checks _ _ w montName roundName

theorem test {mont round : Prog isa} (Hm : stackUse mont ≤ 56) (Hr : stackUse round ≤ 96)
    (w : Nat) (montName roundName : String) : stackUse (CandidateTest.code w montName mont roundName round) ≤ 136 :=
  testOf Hm Hr _ w montName roundName

theorem candidateExponent (w : Nat) : stackUse (CandidateExponent.code w) = 20 := rfl

theorem prepareAndTest {mont round : Prog isa} (Hm : stackUse mont ≤ 56) (Hr : stackUse round ≤ 96)
    (w : Nat) (montName roundName : String) : stackUse (Candidate.prepareAndTest w montName mont roundName round) ≤ 136 := by
  have bound := test Hm Hr w montName roundName
  change max (stackUse (CandidateTest.code w montName mont roundName round)) 0 ≤ 136
  omega

theorem exponentCheck {mont round : Prog isa} (Hm : stackUse mont ≤ 56) (Hr : stackUse round ≤ 96)
    (w : Nat) (montName roundName : String) : stackUse (Candidate.exponentCheck w montName mont roundName round) ≤ 136 := by
  have bound := prepareAndTest Hm Hr w montName roundName
  change max (stackUse (CandidateExponent.code w)) (max 0 (max 0 (stackUse (Candidate.prepareAndTest w montName mont roundName round)))) ≤ 136
  rw [candidateExponent]
  omega

theorem sieveCheck {mont round : Prog isa} (Hm : stackUse mont ≤ 56) (Hr : stackUse round ≤ 96)
    (w : Nat) (montName roundName : String) : stackUse (Candidate.sieveCheck w montName mont roundName round) ≤ 136 := by
  have bound := exponentCheck Hm Hr w montName roundName
  have sieve : stackUse (CandidateSieve.code w) = 24 := rfl
  change max (stackUse (CandidateSieve.code w)) (max 0 (max 0 (stackUse (Candidate.exponentCheck w montName mont roundName round)))) ≤ 136
  rw [sieve]
  omega

theorem sized {mont round : Prog isa} (Hm : stackUse mont ≤ 56) (Hr : stackUse round ≤ 96)
    (w : Nat) (montName roundName : String) : stackUse (Candidate.sized w montName mont roundName round) ≤ 136 := by
  have bound := sieveCheck Hm Hr w montName roundName
  change max 0 (max 0 (max 0 (max 0 (stackUse (Candidate.sieveCheck w montName mont roundName round))))) ≤ 136
  omega

theorem dispatch {mont round : Prog isa} (Hm : stackUse mont ≤ 56) (Hr : stackUse round ≤ 96)
    (montName roundName : String) (widths : List Nat) : stackUse (Candidate.dispatch montName mont roundName round widths) ≤ 136 := by
  induction widths with
  | nil => exact Nat.zero_le _
  | cons w rest ih =>
    have bound := sized Hm Hr w montName roundName
    change max 0 (max (stackUse (Candidate.sized w montName mont roundName round))
      (stackUse (Candidate.dispatch montName mont roundName round rest))) ≤ 136
    omega

theorem body {mont round : Prog isa} (Hm : stackUse mont ≤ 56) (Hr : stackUse round ≤ 96)
    (montName roundName : String) : stackUse (Candidate.body montName mont roundName round) ≤ 136 := by
  have bound := dispatch Hm Hr montName roundName Candidate.widths
  change max 0 (max 0 (max 0 (max 0 (max 0 (stackUse (Candidate.dispatch montName mont roundName round Candidate.widths)))))) ≤ 136
  omega

theorem code {mont round : Prog isa} (Hm : stackUse mont ≤ 56) (Hr : stackUse round ≤ 96)
    (montName roundName : String) : stackUse (Candidate.code montName mont roundName round) ≤ 152 := by
  have bound := body Hm Hr montName roundName
  change max (stackUse (Candidate.body montName mont roundName round)) 0 + 16 ≤ 152
  omega

end VG.Proof.RsaKeyGen.X86.CandidateStackUse
