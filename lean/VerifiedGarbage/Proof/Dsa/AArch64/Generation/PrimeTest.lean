module

public import VerifiedGarbage.Proof.Dsa.AArch64.ProbablePrime.Params
public import VerifiedGarbage.Proof.Framework.AArch64.Depth

/-! # The probable-prime tests parameter generation calls

`vg_dsa_probable_prime_{bits}` for each candidate width: each one's name,
its code, its proof, and the stack its frames use. -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64

structure PrimeTest where
  name : Nat → String
  code : Nat → Prog isa
  verified : ∀ bits, ProbablePrime.Supported bits →
    Verified target (code bits) (ProbablePrime.contract bits)
  depth : ∀ bits, 16 * (code bits).aarch64Depth ≤ ProbablePrime.stack

/-- The call of the test of `bits` bits. -/
def PrimeTest.run (T : PrimeTest) (bits : Nat) : Prog isa := .call (T.name bits) (T.code bits)

end VG.Proof.Dsa.AArch64.Generation
