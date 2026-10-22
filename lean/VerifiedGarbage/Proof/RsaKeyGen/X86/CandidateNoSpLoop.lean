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

theorem witnessRound {mont round : Prog isa} (Hm : NoSp mont) (Hr : NoSp round)
    (w : Nat) (montName roundName : String) : NoSp (WitnessRound.code w montName mont roundName round) := by
  unfold WitnessRound.code WitnessMont.code
  exact sequence (NoSp.of_all (by rfl)) (sequence (NoSp.of_all (by rfl))
    (sequence (sequence (mulY Hm montName 4) (NoSp.of_all (by rfl))) (roundCall Hr roundName)))

theorem witness {mont round : Prog isa} (Hm : NoSp mont) (Hr : NoSp round)
    (w : Nat) (montName roundName : String) : NoSp (WitnessStep.code w montName mont roundName round) := by
  unfold WitnessStep.code
  exact sequence (NoSp.of_all (by rfl))
    (sequence (witnessRound Hm Hr w montName roundName) (NoSp.of_all (by rfl)))

theorem millerRabinOf {mont round : Prog isa} (Hm : NoSp mont) (Hr : NoSp round)
    (checks w : Nat) (montName roundName : String) :
    NoSp (MillerRabinLoop.codeOf checks w montName mont roundName round) := by
  apply NoSp.of_all
  simp only [MillerRabinLoop.codeOf, MillerRabinLoop.step, Code.allInstrs, checked (witness Hm Hr w montName roundName)]
  rfl

theorem millerRabin {mont round : Prog isa} (Hm : NoSp mont) (Hr : NoSp round)
    (w : Nat) (montName roundName : String) : NoSp (MillerRabinLoop.code w montName mont roundName round) :=
  millerRabinOf Hm Hr _ w montName roundName

theorem coreOf {mont round : Prog isa} (Hm : NoSp mont) (Hr : NoSp round)
    (checks w : Nat) (montName roundName : String) : NoSp (CandidateTest.coreOf checks w montName mont roundName round) :=
  sequence (prepare Hm w montName) (millerRabinOf Hm Hr checks w montName roundName)

theorem core {mont round : Prog isa} (Hm : NoSp mont) (Hr : NoSp round)
    (w : Nat) (montName roundName : String) : NoSp (CandidateTest.core w montName mont roundName round) :=
  coreOf Hm Hr _ w montName roundName

theorem testOf {mont round : Prog isa} (Hm : NoSp mont) (Hr : NoSp round)
    (checks w : Nat) (montName roundName : String) : NoSp (CandidateTest.codeOf checks w montName mont roundName round) := by
  apply NoSp.of_all
  simp only [CandidateTest.codeOf, CandidateFrame.code, Code.allInstrs, checked (coreOf Hm Hr checks w montName roundName)]
  rfl

theorem test {mont round : Prog isa} (Hm : NoSp mont) (Hr : NoSp round)
    (w : Nat) (montName roundName : String) : NoSp (CandidateTest.code w montName mont roundName round) :=
  testOf Hm Hr _ w montName roundName

end VG.Proof.RsaKeyGen.X86.CandidateNoSp
