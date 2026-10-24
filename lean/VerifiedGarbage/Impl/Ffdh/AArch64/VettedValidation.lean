module

public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Policy
public import VerifiedGarbage.Impl.Ffdh.AArch64.Domain

/-! Exact standard-domain recognition precedes the unchanged general validator.
Every byte of p, g, and an optional q participates in the comparison. -/
@[expose] public section
namespace VG.Impl.Ffdh.AArch64.VettedValidation
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached

def entry : List Instr :=
  [st .x0 .x3 (8*sDom), st .x1 .x3 (8*sDL), st .x2 .x3 (8*sLen),
   st .x4 .x3 (8*sCtx), mov .x0 .x3, movi .x10 4095, sth .x10 sBits,
   .adrSym .x4 Policy.tableSym, movi .x7 10]

def restore : List Instr :=
  [ldh .x1 sDL, ldh .x2 sLen, ldh .x4 sCtx, mov .x3 .x0, ldh .x0 sDom]

def recognize : Prog isa := .seq (.block entry)
  (.seq (.loop Policy.record (.nonzero .x .x7))
    (.block [ldh .x10 sBits, .subImm .x .x10 .x10 4095]))

def code (window select : Prog isa) (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq recognize (.ite (.nonzero .x .x10) (.block [movi .x0 1])
    (.seq (.block restore) (Domain.CheckDomain.code window select mul)))

end VG.Impl.Ffdh.AArch64.VettedValidation
