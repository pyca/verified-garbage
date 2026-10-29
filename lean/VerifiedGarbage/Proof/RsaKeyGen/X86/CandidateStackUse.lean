module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Candidate
public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateTest
public import VerifiedGarbage.Proof.Framework.X86.Call

import VerifiedGarbage.Impl.RsaKeyGen.X86.Prepare
/-! # Native candidate generation uses at most 152 bytes below its caller -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/CandidateStackUsePrepare.lean`, which only this module imported.
section

/-! # Prepared arithmetic reserves 80 bytes below its caller -/

section
namespace VG.Proof.RsaKeyGen.X86.CandidateStackUse
open VG VG.X86 VG.Impl.RsaKeyGen.X86

theorem mulY {mont : Prog isa} (bound : stackUse mont ≤ 56) (name : String) (array : Nat) :
    stackUse (VG.Impl.MillerRabin.X86.mulY name mont array) ≤ 80 := by
  change max 0 (stackUse mont + 4 + 20) ≤ 80
  omega

theorem six {square : Prog isa} {limit : Nat} (bound : stackUse square ≤ limit) :
    stackUse (VG.Impl.Rsa.X86.Keys.seqs (List.replicate 6 square)) ≤ limit := by
  change max (stackUse square) (max (stackUse square) (max (stackUse square)
    (max (stackUse square) (max (stackUse square) (stackUse square))))) ≤ limit
  omega

theorem fastR2At {square : Prog isa} {limit : Nat} (bound : stackUse square ≤ limit)
    (M : VG.Impl.Mont.Mod) (e acc out : Nat) : stackUse (FastR2.codeAt M e acc out square) ≤ limit := by
  have doubles : stackUse (FastR2.doublesAt M e acc out) = 0 := rfl
  have copies := six bound
  change max (stackUse (FastR2.doublesAt M e acc out))
    (stackUse (VG.Impl.Rsa.X86.Keys.seqs (List.replicate 6 square))) ≤ limit
  rw [doubles]
  omega

theorem fastR2 {square : Prog isa} {limit : Nat} (bound : stackUse square ≤ limit)
    (M : VG.Impl.Mont.Mod) (acc out : Nat) : stackUse (FastR2.code M acc out square) ≤ limit :=
  fastR2At bound M _ acc out

theorem r2At {mont : Prog isa} (bound : stackUse mont ≤ 56) (e w : Nat) (name : String) :
    stackUse (PreparedR2.codeAt e w name mont) ≤ 80 := by
  have main := fastR2At (mulY bound name 6) (VG.Impl.Bignum.X86.PublicContext.modulus w) e
    (VG.Impl.Bignum.X86.PublicContext.slot w 2) (VG.Impl.Bignum.X86.PublicContext.slot w 6)
  change max (stackUse (FastR2.codeAt _ _ _ _ _)) 0 ≤ 80
  omega

theorem r2 {mont : Prog isa} (bound : stackUse mont ≤ 56) (w : Nat) (name : String) :
    stackUse (PreparedR2.code w name mont) ≤ 80 :=
  r2At bound _ w name

theorem lowPairs (src start count : Nat) : stackUse (LowPair.steps src start count) = 0 := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
    change max 0 (stackUse (LowPair.steps src (start + 1) count)) = 0
    rw [ih]; rfl

theorem exponent (w minusOne src out : Nat) : stackUse (Exponent.code w minusOne src out) = 0 := by
  unfold Exponent.code ExponentMarker.code LowPair.scan
  simp only [stackUse, lowPairs]
  rfl

theorem constants {mont : Prog isa} (bound : stackUse mont ≤ 56) (w : Nat) (name : String) :
    stackUse (Constants.code w name mont) ≤ 80 := by
  have product := mulY bound name 4
  change max 0 (max (stackUse (VG.Impl.MillerRabin.X86.mulY name mont 4)) (max 0 0)) ≤ 80
  omega

theorem prepareAt {mont : Prog isa} (bound : stackUse mont ≤ 56) (e w : Nat) (name : String) :
    stackUse (Prepare.codeAt e w name mont) ≤ 80 := by
  have r2bound := r2At bound e w name
  have constantsBound := constants bound w name
  have exponentZero := exponent w (VG.Impl.Bignum.X86.PublicContext.slot w 5)
    (VG.Impl.Bignum.X86.PublicContext.slot w 0) (VG.Impl.Bignum.X86.PublicContext.slot w 27)
  change max 0 (max (stackUse (PreparedR2.codeAt e w name mont))
    (max (stackUse (Constants.code w name mont)) (stackUse (Exponent.code w _ _ _)))) ≤ 80
  rw [exponentZero]
  omega

theorem prepare {mont : Prog isa} (bound : stackUse mont ≤ 56) (w : Nat) (name : String) :
    stackUse (Prepare.code w name mont) ≤ 80 :=
  prepareAt bound _ w name

end VG.Proof.RsaKeyGen.X86.CandidateStackUse
end

end

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

theorem mrExponent : stackUse MrExponentRt.code = 20 := rfl

theorem r2Rt {mont : Prog isa} (Hm : stackUse mont ≤ 56) (montName : String) :
    stackUse (PrepareRt.r2 montName mont) ≤ 80 := by
  have squares := six (mulY Hm montName 6)
  have seed : stackUse PrepareRt.seed = 0 := rfl
  have doubles : stackUse PrepareRt.doubles = 20 := rfl
  have copy : stackUse (VG.Impl.MillerRabin.X86.copy 4 6) = 0 := rfl
  change max (max (stackUse PrepareRt.seed) (max (stackUse PrepareRt.doubles)
    (stackUse (VG.Impl.Rsa.X86.Keys.seqs (List.replicate 6 (VG.Impl.MillerRabin.X86.mulY montName mont 6))))))
    (stackUse (VG.Impl.MillerRabin.X86.copy 4 6)) ≤ 80
  omega

theorem constantsRt {mont : Prog isa} (Hm : stackUse mont ≤ 56) (montName : String) :
    stackUse (PrepareRt.constants montName mont) ≤ 80 := by
  have product := mulY Hm montName 4
  have one : stackUse PrepareRt.one = 0 := rfl
  have copy : stackUse (VG.Impl.MillerRabin.X86.copy 9 6) = 0 := rfl
  have subtract : stackUse PrepareRt.subtract = 20 := rfl
  change max (stackUse PrepareRt.one) (max (stackUse (VG.Impl.MillerRabin.X86.mulY montName mont 4))
    (max (stackUse (VG.Impl.MillerRabin.X86.copy 9 6)) (stackUse PrepareRt.subtract))) ≤ 80
  omega

theorem prepareHead {mont : Prog isa} (Hm : stackUse mont ≤ 56) (montName : String) :
    stackUse (Candidate.prepareHead montName mont) ≤ 80 := by
  have r2bound := r2Rt Hm montName
  have constantsBound := constantsRt Hm montName
  change max (stackUse (PrepareRt.r2 montName mont)) (stackUse (PrepareRt.constants montName mont)) ≤ 80
  omega

theorem prepared {mont : Prog isa} (Hm : stackUse mont ≤ 56) (montName : String) :
    stackUse (Candidate.prepared montName mont) ≤ 80 := by
  have bound := prepareHead Hm montName
  have header : stackUse HeaderRt.prepare = 0 := rfl
  change max (stackUse HeaderRt.prepare) (max (stackUse (Candidate.prepareHead montName mont))
    (stackUse MrExponentRt.code)) ≤ 80
  rw [mrExponent, header]
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
