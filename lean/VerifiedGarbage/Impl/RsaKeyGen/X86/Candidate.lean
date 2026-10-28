module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateArgs
public import VerifiedGarbage.Impl.RsaKeyGen.X86.ExponentRt
public import VerifiedGarbage.Impl.RsaKeyGen.X86.MrExponentRt
public import VerifiedGarbage.Impl.RsaKeyGen.X86.FrontRt
public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessRt
public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateTest
public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateFinish
public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateClear
public import VerifiedGarbage.Impl.Mont.X86.Compact

/-! # Native RSA candidate generation with shared prepared Montgomery calls

The outer frame saves the four cdecl registers. Filters own short frames;
preparation and every witness share one frame containing the Montgomery
callee's capacity slot. Argument copying retains the used-output pointer
outside the header fields overwritten by the prepared round.
-/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Bignum.X86.PublicContext

def clear : Prog isa := CandidateClear.code

/-- The code for the width in `eax`, from the supported `widths`. -/
def dispatch (part : Nat → Prog isa) : List Nat → Prog isa
  | [] => CandidateFinish.none
  | w :: rest => .seq (.block [.alu .cmp .eax (.imm (BitVec.ofNat 32 w))])
      (.ite .e (part w) (dispatch part rest))

def widths : List Nat := (List.range 61).map (· + 4)

/-- `eax := w`, from the candidate's length in the header. -/
def width : List Instr := [.mov .eax (.mem (sc 4)), .shift .shr .eax 3]

/-- Preparation at width `w` but for the exponent: the header, R² and the constants. -/
def prepareHead (w : Nat) (montName : String) (montCode : Prog isa) : Prog isa :=
  .seq (PrepareHeader.code w) (.seq (PreparedR2.code w montName montCode) (Constants.code w montName montCode))

/-- Preparation, with the exponent at the run-time width. -/
def prepared (montName : String) (montCode : Prog isa) : Prog isa :=
  .seq (.block width) (.seq (dispatch (fun w => prepareHead w montName montCode) widths) MrExponentRt.code)

/-- Preparation, then the witnesses. -/
def testBody (montName : String) (montCode : Prog isa) (roundName : String) (roundCode : Prog isa) : Prog isa :=
  .seq (prepared montName montCode) (WitnessRt.code montName montCode roundName roundCode)

/-- Miller–Rabin's result: its code is the same at every width, since
`slot w 0` is 256. -/
def tested (montName : String) (montCode : Prog isa) (roundName : String) (roundCode : Prog isa) : Prog isa :=
  .seq (CandidateFrame.code (testBody montName montCode roundName roundCode)) (CandidateFinish.mrResult 0)

/-- Coprimality with `e`, at the run-time width, then Miller–Rabin. -/
def exponentCheck (montName : String) (montCode : Prog isa)
    (roundName : String) (roundCode : Prog isa) : Prog isa :=
  .seq ExponentRt.code (.seq (.block [.alu .cmp .eax (.imm 0)])
    (.ite .e (CandidateFinish.used 3) (tested montName montCode roundName roundCode)))

def available (montName : String) (montCode : Prog isa) (roundName : String) (roundCode : Prog isa) : Prog isa :=
  .seq FrontRt.code (.seq (.block [.alu .cmp .eax (.imm 4)])
    (.ite .e (exponentCheck montName montCode roundName roundCode) (.block [])))

def body (montName : String) (montCode : Prog isa) (roundName : String) (roundCode : Prog isa) : Prog isa :=
  .seq CandidateArgs.enter (.seq clear
    (.seq (.block [.mov .eax (.mem (sc 32)), .alu .cmp .eax (.mem (sc 4))])
      (.ite .b CandidateFinish.none (available montName montCode roundName roundCode))))

def code (montName : String) (montCode : Prog isa) (roundName : String) (roundCode : Prog isa) : Prog isa :=
  .frame (.push [.ebx, .ebp, .esi, .edi])
    (.seq (body montName montCode roundName roundCode) (.block Compact.restoreRegs)) (.pop .ebx 4)

end VG.Impl.RsaKeyGen.X86.Candidate
