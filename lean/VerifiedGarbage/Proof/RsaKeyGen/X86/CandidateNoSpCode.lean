module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Candidate
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateNoSpLoop
import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64FramedTiming
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

theorem filterGeneral (w : Nat) : NoSp (ExponentFilter.general w) := by
  apply NoSp.of_all
  simp only [ExponentFilter.general, Code.allInstrs,
    checked (VG.Proof.RsaKeyGen.X86.Mod64.array_noSp (2 * w) (slot w 5) 128)]
  rfl

theorem filter (w : Nat) : NoSp (ExponentFilter.code w) := by
  apply NoSp.of_all
  simp only [ExponentFilter.code, Code.allInstrs, checked (filterGeneral w)]
  rfl

theorem candidateExponent (w : Nat) : NoSp (CandidateExponent.code w) := by
  unfold CandidateExponent.code
  exact sequence (NoSp.of_all (by rfl)) (sequence (NoSp.of_all (by rfl)) (filter w))

theorem prepareAndTest {mont round : Prog isa} (Hm : NoSp mont) (Hr : NoSp round)
    (w : Nat) (montName roundName : String) : NoSp (Candidate.prepareAndTest w montName mont roundName round) :=
  sequence (test Hm Hr w montName roundName) (NoSp.of_all (by rfl))

theorem exponentCheck {mont round : Prog isa} (Hm : NoSp mont) (Hr : NoSp round)
    (w : Nat) (montName roundName : String) : NoSp (Candidate.exponentCheck w montName mont roundName round) := by
  apply NoSp.of_all
  simp only [Candidate.exponentCheck, Code.allInstrs, checked (candidateExponent w),
    checked (prepareAndTest Hm Hr w montName roundName)]
  rfl

theorem sieveCheck {mont round : Prog isa} (Hm : NoSp mont) (Hr : NoSp round)
    (w : Nat) (montName roundName : String) : NoSp (Candidate.sieveCheck w montName mont roundName round) := by
  apply NoSp.of_all
  simp only [Candidate.sieveCheck, Code.allInstrs, checked (exponentCheck Hm Hr w montName roundName)]
  rfl

theorem sized {mont round : Prog isa} (Hm : NoSp mont) (Hr : NoSp round)
    (w : Nat) (montName roundName : String) : NoSp (Candidate.sized w montName mont roundName round) := by
  apply NoSp.of_all
  simp only [Candidate.sized, Code.allInstrs, checked (sieveCheck Hm Hr w montName roundName)]
  rfl

theorem dispatch {mont round : Prog isa} (Hm : NoSp mont) (Hr : NoSp round)
    (montName roundName : String) (widths : List Nat) : NoSp (Candidate.dispatch montName mont roundName round widths) := by
  induction widths with
  | nil => exact NoSp.of_all (by rfl)
  | cons w rest ih =>
    apply NoSp.of_all
    simp only [Candidate.dispatch, Code.allInstrs, checked (sized Hm Hr w montName roundName), checked ih]
    rfl

theorem available {mont round : Prog isa} (Hm : NoSp mont) (Hr : NoSp round)
    (montName roundName : String) : NoSp (Candidate.available montName mont roundName round) :=
  sequence (NoSp.of_all (by rfl)) (dispatch Hm Hr montName roundName Candidate.widths)

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
