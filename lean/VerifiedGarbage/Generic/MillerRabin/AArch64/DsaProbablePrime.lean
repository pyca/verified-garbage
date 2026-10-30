module

public import VerifiedGarbage.Proof.Dsa.AArch64.ProbablePrime.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # DSA's probable-prime tests call every shared AArch64 Miller–Rabin implementation

One function for each candidate size DSA parameter generation tests: q of
160 and 256 bits, p of 1024, 2048 and 3072 bits. Every hash backend's
parameter generation calls them, rather than inlining the test. -/

@[expose] public section
namespace VG.Generic.MillerRabin.AArch64.DsaProbablePrime
open VG VG.Proof.Dsa.AArch64.ProbablePrime

def artifacts (v : Proof.MillerRabin.AArch64.RoundImpl) : List Artifact :=
  ([160, 256, 1024, 2048, 3072] : List Nat).attach.map fun (b : { n : Nat // n ∈ ([160, 256, 1024, 2048, 3072] : List Nat) }) =>
    (Spec.Dsa.ProbablePrime.api (Impl.Dsa.AArch64.ProbablePrime.layout b.val)).artifact AArch64.target {
      suffix := v.suffix
      stack := 272
      code := testCode v b.val
      verified := verified v (Supported.of_mem b.property)
      features := v.features }

end VG.Generic.MillerRabin.AArch64.DsaProbablePrime
