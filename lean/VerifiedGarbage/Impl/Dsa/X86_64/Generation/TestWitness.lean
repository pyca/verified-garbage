module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Load
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Uniform
public import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.WitnessRange

/-! # Classify a truncated draw before the RSA forced-witness branch -/

@[expose] public section
namespace VG.Impl.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate

def testWitness : Prog isa := seqs [loadPadded aXm kOut kUsedP,
  Ffdh.X86_64.ParameterCandidate.witnessRange, .block saveUniform]

end VG.Impl.Dsa.X86_64.Generation
