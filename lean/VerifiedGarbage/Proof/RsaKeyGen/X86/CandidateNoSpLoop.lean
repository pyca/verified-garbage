module

import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateNoSpPrepare
public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateTest
public import VerifiedGarbage.Impl.Mont.X86
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateNoSpWords

/-! # All blinded witness calls and their enclosing candidate frame preserve ESP -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.CandidateNoSp
open VG VG.X86 VG.Impl.RsaKeyGen.X86

theorem roundCall {round : Prog isa} (H : NoSp round) (name : String) : NoSp (RoundCall.code name round) := by
  apply NoSp.of_all
  simp only [RoundCall.code, RoundCall.call, Code.allInstrs, checked H]
  rfl

theorem witnessZeros (o n : Nat) : NoSp (.block (WitnessLoad.zeros o n)) := by
  apply NoSp.of_all
  rw [Code.allInstrs_eq]
  simp only [instrs, WitnessLoad.zeros, List.all_flatMap, List.all_eq_true, List.mem_range]
  intro _ _ x mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl <;> rfl

theorem witnessLoadAt (D k w : Nat) : NoSp (WitnessLoad.codeAt D k w) := by
  unfold WitnessLoad.codeAt WitnessLoad.zeroTail
  exact sequence (NoSp.of_all (by rfl)) (sequence (witnessZeros _ _) (NoSp.of_all (by rfl)))

theorem witnessRoundAt {mont round : Prog isa} (Hm : NoSp mont) (Hr : NoSp round)
    (D k w : Nat) (montName roundName : String) : NoSp (WitnessRound.codeAt D k w montName mont roundName round) := by
  unfold WitnessRound.codeAt WitnessMont.code
  exact sequence (witnessLoadAt D k w) (sequence (NoSp.of_all (by rfl))
    (sequence (sequence (mulY Hm montName 4) (NoSp.of_all (by rfl))) (roundCall Hr roundName)))

theorem witnessAt {mont round : Prog isa} (Hm : NoSp mont) (Hr : NoSp round)
    (D k w : Nat) (montName roundName : String) : NoSp (WitnessStep.codeAt D k w montName mont roundName round) := by
  unfold WitnessStep.codeAt
  exact sequence (NoSp.of_all (by rfl))
    (sequence (witnessRoundAt Hm Hr D k w montName roundName) (NoSp.of_all (by rfl)))

theorem witness {mont round : Prog isa} (Hm : NoSp mont) (Hr : NoSp round)
    (w : Nat) (montName roundName : String) : NoSp (WitnessStep.code w montName mont roundName round) :=
  witnessAt Hm Hr _ _ w montName roundName

theorem millerRabinWith {mont round : Prog isa} (Hm : NoSp mont) (Hr : NoSp round)
    (checks D k w : Nat) (montName roundName : String) :
    NoSp (MillerRabinLoop.codeWith checks D k w montName mont roundName round) := by
  apply NoSp.of_all
  simp only [MillerRabinLoop.codeWith, MillerRabinLoop.stepAt, Code.allInstrs,
    checked (witnessAt Hm Hr D k w montName roundName)]
  rfl

theorem millerRabinOf {mont round : Prog isa} (Hm : NoSp mont) (Hr : NoSp round)
    (checks w : Nat) (montName roundName : String) :
    NoSp (MillerRabinLoop.codeOf checks w montName mont roundName round) :=
  millerRabinWith Hm Hr checks _ _ w montName roundName

theorem millerRabin {mont round : Prog isa} (Hm : NoSp mont) (Hr : NoSp round)
    (w : Nat) (montName roundName : String) : NoSp (MillerRabinLoop.code w montName mont roundName round) :=
  millerRabinOf Hm Hr _ w montName roundName

theorem coreWith {mont round : Prog isa} (Hm : NoSp mont) (Hr : NoSp round)
    (e checks D k w : Nat) (montName roundName : String) :
    NoSp (CandidateTest.coreWith e checks D k w montName mont roundName round) :=
  sequence (prepareAt Hm e w montName) (millerRabinWith Hm Hr checks D k w montName roundName)

theorem coreOf {mont round : Prog isa} (Hm : NoSp mont) (Hr : NoSp round)
    (checks w : Nat) (montName roundName : String) : NoSp (CandidateTest.coreOf checks w montName mont roundName round) :=
  coreWith Hm Hr _ checks _ _ w montName roundName

theorem core {mont round : Prog isa} (Hm : NoSp mont) (Hr : NoSp round)
    (w : Nat) (montName roundName : String) : NoSp (CandidateTest.core w montName mont roundName round) :=
  coreOf Hm Hr _ w montName roundName

theorem testWith {mont round : Prog isa} (Hm : NoSp mont) (Hr : NoSp round)
    (e checks D k w : Nat) (montName roundName : String) :
    NoSp (CandidateTest.codeWith e checks D k w montName mont roundName round) := by
  apply NoSp.of_all
  simp only [CandidateTest.codeWith, CandidateFrame.code, Code.allInstrs,
    checked (coreWith Hm Hr e checks D k w montName roundName)]
  rfl

theorem testOf {mont round : Prog isa} (Hm : NoSp mont) (Hr : NoSp round)
    (checks w : Nat) (montName roundName : String) : NoSp (CandidateTest.codeOf checks w montName mont roundName round) :=
  testWith Hm Hr _ checks _ _ w montName roundName

theorem test {mont round : Prog isa} (Hm : NoSp mont) (Hr : NoSp round)
    (w : Nat) (montName roundName : String) : NoSp (CandidateTest.code w montName mont roundName round) :=
  testOf Hm Hr _ w montName roundName

end VG.Proof.RsaKeyGen.X86.CandidateNoSp
