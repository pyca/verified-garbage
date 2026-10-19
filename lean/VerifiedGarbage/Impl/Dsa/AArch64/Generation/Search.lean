module

public import VerifiedGarbage.Impl.RsaKeyGen.AArch64.Candidate

/-! Bounded p search with a separate counter, seed offset and status block. -/
@[expose] public section
namespace VG.Impl.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate

def pSearchInit : List Instr :=
  [movi .x3 0, sth .x3 0, movi .x3 1, sth .x3 1]

def pSearchAdvanceHead (limit stride : Nat) : List Instr :=
  [ldh .x3 0, .addImm .x .x3 .x3 1, sth .x3 0,
   ldh .x4 1, .addImm .x .x4 .x4 stride, sth .x4 1, movi .x4 limit] ++ geFlag

def pSearchStatus (status : Nat) : List Instr := [movi .x3 status, sth .x3 2]

def pSearchAdvance (limit stride : Nat) : Prog isa :=
  .seq (.block (pSearchAdvanceHead limit stride))
    (.ite (.zero .x .x5) (.block (pSearchStatus 3)) (.block (pSearchStatus 2)))

def pSearchStatusCmp : List Instr := [ldh .x3 2, .subImm .x .x3 .x3 3]

def pSearchIteration (body : Prog isa) (limit stride : Nat) : Prog isa := seqs [
  body, .block pSearchStatusCmp,
  .ite (.zero .x .x3) (pSearchAdvance limit stride) (.block []), .block pSearchStatusCmp]

def pSearch (body : Prog isa) (limit stride : Nat) : Prog isa :=
  .seq (.block pSearchInit) (.loop (pSearchIteration body limit stride) (.zero .x .x3))

end VG.Impl.Dsa.AArch64.Generation
