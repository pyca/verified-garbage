module

public import VerifiedGarbage.Proof.Dsa.X86_64.ProbablePrime.Params
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CodeSafety
public import VerifiedGarbage.Proof.Framework.X86_64.Depth

/-! # The probable-prime tests parameter generation calls

`vg_dsa_probable_prime_{bits}` for each candidate width: each one's name,
its code, its proof, and what calling it requires of it. -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64

structure PrimeTest where
  name : Nat → String
  code : Nat → Prog isa
  verified : ∀ bits, ProbablePrime.Supported bits →
    Verified target (code bits) (ProbablePrime.contract bits)
  safe : ∀ bits, generationSafe (code bits)
  depth : ∀ bits, (code bits).x86_64Depth ≤ ProbablePrime.stack

/-- The call of the test of `bits` bits. -/
def PrimeTest.run (T : PrimeTest) (bits : Nat) : Prog isa := .call (T.name bits) (T.code bits)

end VG.Proof.Dsa.X86_64.Generation
