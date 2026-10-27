module

public import VerifiedGarbage.Proof.Dsa.X86_64.ProbablePrime.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # DSA's probable-prime test calls every shared x86-64 Miller–Rabin implementation

One function for every candidate size DSA parameter generation tests: q of
160 and 256 bits, p of 1024, 2048 and 3072 bits, the size an argument. Every
hash backend's parameter generation calls it, rather than inlining the test. -/

@[expose] public section
namespace VG.Generic.MillerRabin.X86_64.DsaProbablePrime
open VG VG.Proof.Dsa.X86_64.ProbablePrime

def artifacts (v : Proof.MillerRabin.X86_64.RoundImpl) : List Artifact :=
  [(Spec.Dsa.ProbablePrime.sizedApi Impl.Dsa.X86_64.ProbablePrime.layout
      Impl.Dsa.X86_64.ProbablePrime.sizes).artifact X86_64.target {
    suffix := v.suffix
    notes := ["Parameter generation's test on the candidate at its size's offset of the generation's \
      scratch space: trial division, then the blinded Miller–Rabin loop calling the shared round, with \
      the arithmetic of the round's implementation. The size's words, octets, offset, draw and \
      witness count are derived from `bits` on entry, without a branch, into the arithmetic \
      workspace's header. A 56-byte frame keeps the callee-saved registers and `used`."]
    stack := 184
    code := testCode v
    verified := verified v
    spSafe := (testCode_safe v).sp
    features := v.features }]

end VG.Generic.MillerRabin.X86_64.DsaProbablePrime
