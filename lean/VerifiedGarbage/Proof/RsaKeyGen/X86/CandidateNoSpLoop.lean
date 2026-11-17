module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateTest
public import VerifiedGarbage.Impl.Mont.X86
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Framework.X86.CallWith
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Prepare
public import VerifiedGarbage.Impl.Mont.Mod
public import VerifiedGarbage.Impl.Mont.X86.Words

/-! ### `RsaKeyGen.X86.CandidateNoSpPrepare`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.CandidateNoSpWords`, which this module and modules that import it used -/

section

/-! # Native candidate word initialization never assigns ESP -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.CandidateNoSp
open VG VG.X86 VG.Impl.Mont.X86.Dynamic

theorem sequence {a b : Prog isa} (A : NoSp a) (B : NoSp b) : NoSp (.seq a b) := by
  intro i mem
  rcases List.mem_append.mp mem with mem | mem
  · exact A i mem
  · exact B i mem

theorem zeros (out n : Nat) : NoSp (zerosW out n) := NoSp.of_all (by rfl)

theorem constant (n out value : Nat) : NoSp (setConstW n out value) := by
  unfold setConstW
  apply sequence (zeros out n)
  intro i mem
  obtain ⟨j, _, mem⟩ := List.mem_flatMap.mp mem
  split at mem
  · simp only [List.not_mem_nil] at mem
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl <;> rfl

end VG.Proof.RsaKeyGen.X86.CandidateNoSp

end

end

/-! # Prepared candidate calls and word arithmetic preserve ESP -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.CandidateNoSp
open VG VG.X86 VG.Impl.Mont.X86.Dynamic
open VG.Impl.RsaKeyGen.X86

theorem checked {c : Prog isa} (H : NoSp c) : c.allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  rw [Code.allInstrs_eq, List.all_eq_true]
  intro i mem
  rw [H i mem]
  rfl

theorem mulY {mont : Prog isa} (H : NoSp mont) (name : String) (array : Nat) :
    NoSp (VG.Impl.MillerRabin.X86.mulY name mont array) := by
  apply NoSp.of_all
  simp only [VG.Impl.MillerRabin.X86.mulY, Code.allInstrs, checked H]
  rfl

theorem r2_doublesAt (M : VG.Impl.Mont.Mod) (e acc out : Nat) : NoSp (FastR2.doublesAt M e acc out) := by
  unfold FastR2.doublesAt FastR2.seedAt
  exact sequence (constant _ _ _) (NoSp.of_all (by rfl))

theorem fastR2At {square : Prog isa} (H : NoSp square) (M : VG.Impl.Mont.Mod) (e acc out : Nat) :
    NoSp (FastR2.codeAt M e acc out square) := by
  unfold FastR2.codeAt
  apply sequence (r2_doublesAt M e acc out)
  change NoSp (.seq square (.seq square (.seq square (.seq square (.seq square square)))))
  exact sequence H (sequence H (sequence H (sequence H (sequence H H))))

theorem r2At {mont : Prog isa} (H : NoSp mont) (e w : Nat) (name : String) : NoSp (PreparedR2.codeAt e w name mont) := by
  unfold PreparedR2.codeAt
  exact sequence (fastR2At (mulY H name 6) _ _ _ _) (NoSp.of_all (by rfl))

theorem constants {mont : Prog isa} (H : NoSp mont) (w : Nat) (name : String) : NoSp (Constants.code w name mont) := by
  unfold Constants.code
  exact sequence (NoSp.of_all (by rfl))
    (sequence (mulY H name 4) (sequence (NoSp.of_all (by rfl)) (NoSp.of_all (by rfl))))

theorem lowPairs (src start count : Nat) : NoSp (LowPair.steps src start count) := by
  induction count generalizing start with
  | zero => exact NoSp.of_all (by rfl)
  | succ count ih => exact sequence (NoSp.of_all (by rfl)) (ih _)

theorem exponent (w minusOne src out : Nat) : NoSp (Exponent.code w minusOne src out) := by
  unfold Exponent.code ExponentMarker.code LowPair.scan
  exact sequence (sequence (sequence (NoSp.of_all (by rfl)) (lowPairs minusOne 0 w))
    (NoSp.of_all (by rfl))) (NoSp.of_all (by rfl))

theorem prepareAt {mont : Prog isa} (H : NoSp mont) (e w : Nat) (name : String) :
    NoSp (Prepare.codeAt e w name mont) := by
  unfold Prepare.codeAt
  exact sequence (NoSp.of_all (by rfl)) (sequence (r2At H e w name)
    (sequence (constants H w name) (exponent _ _ _ _)))

end VG.Proof.RsaKeyGen.X86.CandidateNoSp

end

end

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

theorem millerRabinWith {mont round : Prog isa} (Hm : NoSp mont) (Hr : NoSp round)
    (checks D k w : Nat) (montName roundName : String) :
    NoSp (MillerRabinLoop.codeWith checks D k w montName mont roundName round) := by
  apply NoSp.of_all
  simp only [MillerRabinLoop.codeWith, MillerRabinLoop.stepAt, Code.allInstrs,
    checked (witnessAt Hm Hr D k w montName roundName)]
  rfl

theorem coreWith {mont round : Prog isa} (Hm : NoSp mont) (Hr : NoSp round)
    (e checks D k w : Nat) (montName roundName : String) :
    NoSp (CandidateTest.coreWith e checks D k w montName mont roundName round) :=
  sequence (prepareAt Hm e w montName) (millerRabinWith Hm Hr checks D k w montName roundName)

theorem testWith {mont round : Prog isa} (Hm : NoSp mont) (Hr : NoSp round)
    (e checks D k w : Nat) (montName roundName : String) :
    NoSp (CandidateTest.codeWith e checks D k w montName mont roundName round) := by
  apply NoSp.of_all
  simp only [CandidateTest.codeWith, CandidateFrame.code, Code.allInstrs,
    checked (coreWith Hm Hr e checks D k w montName roundName)]
  rfl

end VG.Proof.RsaKeyGen.X86.CandidateNoSp
