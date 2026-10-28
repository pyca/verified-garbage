module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Candidate
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateNoSpLoop
import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentRt.Array
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateNoSpPrepare
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateNoSpWords
public import VerifiedGarbage.Impl.Bignum.X86.PublicContext
public import VerifiedGarbage.Impl.Mont.X86.Compact
public import VerifiedGarbage.Proof.Framework.X86.Call

/-! # The complete native candidate dispatcher preserves ESP inside its frames -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.CandidateNoSp
open VG VG.X86 VG.Impl.RsaKeyGen.X86
open VG.Impl.Bignum.X86.PublicContext

theorem general : NoSp ExponentRt.general := by
  apply NoSp.of_all
  simp only [ExponentRt.general, Code.allInstrs, checked VG.Proof.RsaKeyGen.X86.ExponentRt.array_noSp]
  rfl

theorem exponentRt : NoSp ExponentRt.code := by
  apply NoSp.of_all
  simp only [ExponentRt.code, ExponentRt.filter, Code.allInstrs, checked general]
  rfl

theorem mrExponent : NoSp MrExponentRt.code := NoSp.of_all (by rfl)

theorem r2Rt {mont : Prog isa} (Hm : NoSp mont) (montName : String) :
    NoSp (PrepareRt.r2 montName mont) := by
  unfold PrepareRt.r2
  refine sequence (sequence (NoSp.of_all (by rfl)) (sequence (NoSp.of_all (by rfl)) ?_)) (NoSp.of_all (by rfl))
  have H := mulY Hm montName 6
  change NoSp (.seq _ (.seq _ (.seq _ (.seq _ (.seq _ _)))))
  exact sequence H (sequence H (sequence H (sequence H (sequence H H))))

theorem constantsRt {mont : Prog isa} (Hm : NoSp mont) (montName : String) :
    NoSp (PrepareRt.constants montName mont) := by
  unfold PrepareRt.constants
  exact sequence (NoSp.of_all (by rfl))
    (sequence (mulY Hm montName 4) (sequence (NoSp.of_all (by rfl)) (NoSp.of_all (by rfl))))

theorem prepareHead {mont : Prog isa} (Hm : NoSp mont) (montName : String) :
    NoSp (Candidate.prepareHead montName mont) :=
  sequence (r2Rt Hm montName) (constantsRt Hm montName)

theorem prepared {mont : Prog isa} (Hm : NoSp mont) (montName : String) :
    NoSp (Candidate.prepared montName mont) :=
  sequence (NoSp.of_all (by rfl)) (sequence (prepareHead Hm montName) mrExponent)

theorem witnessRound {mont round : Prog isa} (Hm : NoSp mont) (Hr : NoSp round) (montName roundName : String) :
    NoSp (WitnessRt.round montName mont roundName round) := by
  unfold WitnessRt.round WitnessMont.code
  exact sequence (NoSp.of_all (by rfl)) (sequence (NoSp.of_all (by rfl))
    (sequence (sequence (mulY Hm montName 4) (NoSp.of_all (by rfl))) (roundCall Hr roundName)))

theorem witnessBody {mont round : Prog isa} (Hm : NoSp mont) (Hr : NoSp round) (montName roundName : String) :
    NoSp (WitnessRt.body montName mont roundName round) := by
  unfold WitnessRt.body
  exact sequence (NoSp.of_all (by rfl)) (sequence (witnessRound Hm Hr montName roundName) (NoSp.of_all (by rfl)))

theorem witnesses {mont round : Prog isa} (Hm : NoSp mont) (Hr : NoSp round) (montName roundName : String) :
    NoSp (WitnessRt.code montName mont roundName round) := by
  apply NoSp.of_all
  simp only [WitnessRt.code, WitnessRt.step, Code.allInstrs, checked (witnessBody Hm Hr montName roundName)]
  rfl

theorem testBody {mont round : Prog isa} (Hm : NoSp mont) (Hr : NoSp round) (montName roundName : String) :
    NoSp (Candidate.testBody montName mont roundName round) :=
  sequence (prepared Hm montName) (witnesses Hm Hr montName roundName)

theorem tested {mont round : Prog isa} (Hm : NoSp mont) (Hr : NoSp round) (montName roundName : String) :
    NoSp (Candidate.tested montName mont roundName round) := by
  apply NoSp.of_all
  simp only [Candidate.tested, CandidateFrame.code, Code.allInstrs, checked (testBody Hm Hr montName roundName)]
  rfl

theorem exponentCheck {mont round : Prog isa} (Hm : NoSp mont) (Hr : NoSp round)
    (montName roundName : String) : NoSp (Candidate.exponentCheck montName mont roundName round) := by
  apply NoSp.of_all
  simp only [Candidate.exponentCheck, Code.allInstrs, checked exponentRt, checked (tested Hm Hr montName roundName)]
  rfl

theorem front : NoSp VG.Impl.RsaKeyGen.X86.FrontRt.code := by
  apply NoSp.of_all
  rfl

theorem available {mont round : Prog isa} (Hm : NoSp mont) (Hr : NoSp round)
    (montName roundName : String) : NoSp (Candidate.available montName mont roundName round) := by
  apply NoSp.of_all
  simp only [Candidate.available, Code.allInstrs, checked front,
    checked (exponentCheck Hm Hr montName roundName)]
  rfl

theorem body {mont round : Prog isa} (Hm : NoSp mont) (Hr : NoSp round)
    (montName roundName : String) : NoSp (Candidate.body montName mont roundName round) := by
  apply NoSp.of_all
  simp only [Candidate.body, Code.allInstrs, checked (available Hm Hr montName roundName)]
  rfl

theorem code {mont round : Prog isa} (Hm : NoSp mont) (Hr : NoSp round)
    (montName roundName : String) : NoSp (Candidate.code montName mont roundName round) := by
  apply NoSp.of_all
  simp only [Candidate.code, Code.allInstrs, checked (body Hm Hr montName roundName)]
  rfl

end VG.Proof.RsaKeyGen.X86.CandidateNoSp
