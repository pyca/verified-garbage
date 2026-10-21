module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateArgs
public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateLoad
public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateExponent
public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateSieve
public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateClose
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

def importCandidate (w : Nat) : Prog isa := CandidateLoad.code w

def closeCheck (w : Nat) : Prog isa := CandidateClose.code w

def prepareAndTest (w : Nat) (montName : String) (montCode : Prog isa)
    (roundName : String) (roundCode : Prog isa) : Prog isa :=
  .seq (CandidateTest.code w montName montCode roundName roundCode) (CandidateFinish.mrResult w)

def exponentCheck (w : Nat) (montName : String) (montCode : Prog isa)
    (roundName : String) (roundCode : Prog isa) : Prog isa :=
  .seq (CandidateExponent.code w) (.seq (.block [.alu .cmp .eax (.imm 0)])
    (.ite .e (CandidateFinish.used 3) (prepareAndTest w montName montCode roundName roundCode)))

def sieveCheck (w : Nat) (montName : String) (montCode : Prog isa)
    (roundName : String) (roundCode : Prog isa) : Prog isa :=
  .seq (CandidateSieve.code w) (.seq (.block [.alu .cmp .eax (.imm 0)])
    (.ite .ne (CandidateFinish.used 3) (exponentCheck w montName montCode roundName roundCode)))

def sized (w : Nat) (montName : String) (montCode : Prog isa)
    (roundName : String) (roundCode : Prog isa) : Prog isa :=
  .seq (importCandidate w) (.seq (closeCheck w) (.seq (.block [.alu .cmp .eax (.imm 0)])
    (.ite .ne (CandidateFinish.used 2) (sieveCheck w montName montCode roundName roundCode))))

def dispatch (montName : String) (montCode : Prog isa) (roundName : String) (roundCode : Prog isa) : List Nat → Prog isa
  | [] => CandidateFinish.none
  | w :: rest => .seq (.block [.alu .cmp .eax (.imm (BitVec.ofNat 32 w))])
      (.ite .e (sized w montName montCode roundName roundCode) (dispatch montName montCode roundName roundCode rest))

def widths : List Nat := (List.range 61).map (· + 4)

def available (montName : String) (montCode : Prog isa) (roundName : String) (roundCode : Prog isa) : Prog isa :=
  .seq (.block [.mov .eax (.mem (sc 4)), .shift .shr .eax 3])
    (dispatch montName montCode roundName roundCode widths)

def body (montName : String) (montCode : Prog isa) (roundName : String) (roundCode : Prog isa) : Prog isa :=
  .seq CandidateArgs.enter (.seq clear
    (.seq (.block [.mov .eax (.mem (sc 32)), .alu .cmp .eax (.mem (sc 4))])
      (.ite .b CandidateFinish.none (available montName montCode roundName roundCode))))

def code (montName : String) (montCode : Prog isa) (roundName : String) (roundCode : Prog isa) : Prog isa :=
  .frame (.push [.ebx, .ebp, .esi, .edi])
    (.seq (body montName montCode roundName roundCode) (.block Compact.restoreRegs)) (.pop .ebx 4)

end VG.Impl.RsaKeyGen.X86.Candidate
