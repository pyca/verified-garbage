module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessUniform
public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessFallback

/-! # Match the reviewed uniform-or-forced witness sampler without secret branches -/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.WitnessSample
open VG VG.X86

/-- For a witness of `k` native words in a `w`-word geometry. -/
def codeAt (k w src modulus : Nat) : Prog isa :=
  .seq (WitnessUniform.code w src modulus) (.block (WitnessFallback.codeAt k src))

def code (w src modulus : Nat) : Prog isa := codeAt (2 * w) w src modulus

end VG.Impl.RsaKeyGen.X86.WitnessSample
