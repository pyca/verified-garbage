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

theorem exponentRt : stackUse ExponentRt.code = 20 := rfl

theorem dispatch {part : Nat → Prog isa} {bound : Nat} (H : ∀ w, stackUse (part w) ≤ bound) (widths : List Nat) :
    stackUse (Candidate.dispatch part widths) ≤ bound := by
  induction widths with
  | nil => exact Nat.zero_le _
  | cons w rest ih =>
    have bound := H w
    change max 0 (max (stackUse (part w)) (stackUse (Candidate.dispatch part rest))) ≤ _
    omega

theorem mrExponent : stackUse MrExponentRt.code = 20 := rfl

theorem prepareHead {mont : Prog isa} (Hm : stackUse mont ≤ 56) (w : Nat) (montName : String) :
    stackUse (Candidate.prepareHead w montName mont) ≤ 80 := by
  have r2bound := r2 Hm w montName
  have constantsBound := constants Hm w montName
  change max 0 (max (stackUse (PreparedR2.code w montName mont)) (stackUse (Constants.code w montName mont))) ≤ 80
  omega

theorem prepared {mont : Prog isa} (Hm : stackUse mont ≤ 56) (montName : String) :
    stackUse (Candidate.prepared montName mont) ≤ 80 := by
  have bound := dispatch (fun w => prepareHead Hm w montName) Candidate.widths
  unfold Candidate.prepared
  generalize Candidate.dispatch (fun w => Candidate.prepareHead w montName mont) Candidate.widths = d at bound ⊢
  change max 0 (max (stackUse d) (stackUse MrExponentRt.code)) ≤ 80
  rw [mrExponent]
  omega

theorem witnessRound {mont round : Prog isa} (Hm : stackUse mont ≤ 56) (Hr : stackUse round ≤ 96)
    (montName roundName : String) : stackUse (WitnessRt.round montName mont roundName round) ≤ 108 := by
  have product := mulY Hm montName 4
  have drawn : stackUse WitnessRt.drawn = 0 := rfl
  change max (stackUse WitnessRt.drawn) (max 0 (max (max (stackUse (VG.Impl.MillerRabin.X86.mulY montName mont 4)) 0)
    (max 0 (stackUse round + 4 + 8)))) ≤ 108
  omega

theorem witnesses {mont round : Prog isa} (Hm : stackUse mont ≤ 56) (Hr : stackUse round ≤ 96)
    (montName roundName : String) : stackUse (WitnessRt.code montName mont roundName round) ≤ 108 := by
  have bound := witnessRound Hm Hr montName roundName
  change max 0 (max 0 (max (max 0 (max 0 (max (stackUse (WitnessRt.round montName mont roundName round)) 0))) 0)) ≤ 108
  omega

theorem testBody {mont round : Prog isa} (Hm : stackUse mont ≤ 56) (Hr : stackUse round ≤ 96)
    (montName roundName : String) : stackUse (Candidate.testBody montName mont roundName round) ≤ 108 := by
  have head := prepared Hm montName
  have loop := witnesses Hm Hr montName roundName
  change max (stackUse (Candidate.prepared montName mont)) (stackUse (WitnessRt.code montName mont roundName round)) ≤ 108
  omega

theorem tested {mont round : Prog isa} (Hm : stackUse mont ≤ 56) (Hr : stackUse round ≤ 96)
    (montName roundName : String) : stackUse (Candidate.tested montName mont roundName round) ≤ 136 := by
  have bound := testBody Hm Hr montName roundName
  unfold Candidate.tested CandidateFrame.code
  generalize Candidate.testBody montName mont roundName round = b at bound ⊢
  change max (max 0 (max 0 (stackUse b) + 28)) (stackUse (CandidateFinish.mrResult 0)) ≤ 136
  have result : stackUse (CandidateFinish.mrResult 0) = 0 := rfl
  omega

theorem exponentCheck {mont round : Prog isa} (Hm : stackUse mont ≤ 56) (Hr : stackUse round ≤ 96)
    (montName roundName : String) : stackUse (Candidate.exponentCheck montName mont roundName round) ≤ 136 := by
  have bound := tested Hm Hr montName roundName
  unfold Candidate.exponentCheck
  generalize Candidate.tested montName mont roundName round = d at bound ⊢
  change max (stackUse ExponentRt.code) (max 0 (max 0 (max 0 (stackUse d)))) ≤ 136
  rw [exponentRt]
  omega

theorem front : stackUse VG.Impl.RsaKeyGen.X86.FrontRt.code = 24 := rfl

theorem available {mont round : Prog isa} (Hm : stackUse mont ≤ 56) (Hr : stackUse round ≤ 96)
    (montName roundName : String) : stackUse (Candidate.available montName mont roundName round) ≤ 136 := by
  have exponent := exponentCheck Hm Hr montName roundName
  unfold Candidate.available
  generalize Candidate.exponentCheck montName mont roundName round = e at exponent ⊢
  change max (stackUse VG.Impl.RsaKeyGen.X86.FrontRt.code) (max 0 (max (stackUse e) 0)) ≤ 136
  rw [front]
  omega

theorem body {mont round : Prog isa} (Hm : stackUse mont ≤ 56) (Hr : stackUse round ≤ 96)
    (montName roundName : String) : stackUse (Candidate.body montName mont roundName round) ≤ 136 := by
  have bound := available Hm Hr montName roundName
  unfold Candidate.body
  generalize Candidate.available montName mont roundName round = a at bound ⊢
  change max 0 (max 0 (max 0 (max 0 (max 0 (stackUse a))))) ≤ 136
  omega

theorem code {mont round : Prog isa} (Hm : stackUse mont ≤ 56) (Hr : stackUse round ≤ 96)
    (montName roundName : String) : stackUse (Candidate.code montName mont roundName round) ≤ 152 := by
  have bound := body Hm Hr montName roundName
  unfold Candidate.code
  generalize Candidate.body montName mont roundName round = b at bound ⊢
  change max (stackUse b) 0 + 16 ≤ 152
  omega

end VG.Proof.RsaKeyGen.X86.CandidateStackUse
