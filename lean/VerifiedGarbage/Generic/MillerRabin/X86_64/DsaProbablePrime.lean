module

public import VerifiedGarbage.Proof.Dsa.X86_64.ProbablePrime.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # DSA's probable-prime tests call every shared x86-64 Miller–Rabin implementation

One function for each candidate size DSA parameter generation tests: q of
160 and 256 bits, p of 1024, 2048 and 3072 bits. Every hash backend's
parameter generation calls them, rather than inlining the test. -/

@[expose] public section
namespace VG.Generic.MillerRabin.X86_64.DsaProbablePrime
open VG VG.Proof.Dsa.X86_64.ProbablePrime

def artifacts (v : Proof.MillerRabin.X86_64.RoundImpl) : List Artifact :=
  ([160, 256, 1024, 2048, 3072] : List Nat).attach.map fun (b : { n : Nat // n ∈ ([160, 256, 1024, 2048, 3072] : List Nat) }) =>
    (Spec.Dsa.ProbablePrime.api (Impl.Dsa.X86_64.ProbablePrime.layout b.val)).artifact X86_64.target {
      suffix := v.suffix
      notes := ["Parameter generation's test on the candidate at its offset of the generation's scratch \
        space: trial division, then the blinded Miller–Rabin loop calling the shared round, with the \
        arithmetic of the round's implementation. A 56-byte frame keeps the callee-saved registers \
        and `used`."]
      stack := 184
      code := testCode v b.val
      verified := verified v (Supported.of_mem b.property)
      spSafe := (testCode_safe v b.val).sp
      features := v.features }

end VG.Generic.MillerRabin.X86_64.DsaProbablePrime
