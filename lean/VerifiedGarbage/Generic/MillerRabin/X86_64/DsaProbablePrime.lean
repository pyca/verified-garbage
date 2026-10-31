module

public import VerifiedGarbage.Proof.Dsa.X86_64.ProbablePrime.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # DSA's probable-prime test calls every shared x86-64 Miller–Rabin implementation -/

@[expose] public section
namespace VG.Generic.MillerRabin.X86_64.DsaProbablePrime
open VG VG.Proof.Dsa.X86_64.ProbablePrime

def artifacts (v : Proof.MillerRabin.X86_64.RoundImpl) : List Artifact :=
  [(Spec.Dsa.ProbablePrime.sizedApi Impl.Dsa.X86_64.ProbablePrime.layout
      Impl.Dsa.X86_64.ProbablePrime.sizes).artifact X86_64.target {
    suffix := v.suffix
    stack := 184
    code := testCode v
    verified := verified v
    spSafe := (testCode_safe v).sp
    features := v.features }]

end VG.Generic.MillerRabin.X86_64.DsaProbablePrime
