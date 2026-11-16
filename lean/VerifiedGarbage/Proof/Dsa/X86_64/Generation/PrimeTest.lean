module

public import VerifiedGarbage.Proof.Dsa.X86_64.ProbablePrime.Params
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CodeSafety
public import VerifiedGarbage.Proof.Framework.X86_64.Depth
public import VerifiedGarbage.Proof.Framework.X86_64.ModeSim

/-! # The probable-prime test parameter generation calls

`vg_dsa_probable_prime`, of every candidate width: its name, its code, its
proof, and what calling it requires of it. -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64

structure PrimeTest where
  name : String
  code : Prog isa
  verified : Verified target code ProbablePrime.contract
  safe : generationSafe code
  depth : code.x86_64Depth ≤ ProbablePrime.stack
  /-- It never touches MXCSR, so its callers' runs need not agree on it
  (`Contract.mxFree`). -/
  noMx : code.allInstrs (fun i => !touchesMxcsr i) = true

/-- The call of the test. -/
def PrimeTest.run (T : PrimeTest) : Prog isa := .call T.name T.code

end VG.Proof.Dsa.X86_64.Generation
