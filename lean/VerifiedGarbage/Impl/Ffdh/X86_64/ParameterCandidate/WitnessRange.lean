module

public import VerifiedGarbage.Impl.Ffdh.X86_64.Domain

/-! # FFDH parameter candidates on x86-64: reject witnesses outside [2,N−2] -/

@[expose] public section

namespace VG.Impl.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public

/-- The sampled integer is in aXm. ZF is clear exactly for an accepted draw. -/
def witnessRange : Prog isa := seqs (Domain.rangeTest aXm)

/-- Convert an accepted sampled witness and use the shared prepared round. -/
def witnessRound (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa) : Prog isa :=
  .seq (mul aXm aXm aR2) round

end VG.Impl.Ffdh.X86_64.ParameterCandidate
