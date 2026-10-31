module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generator.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # DSA's generator stages call every shared AArch64 Miller–Rabin implementation

One function for each width of p DSA parameter generation produces: 1024,
2048 and 3072 bits. Every hash backend's parameter generation calls them,
rather than inlining the generator search and the domain check. -/

@[expose] public section
namespace VG.Generic.MillerRabin.AArch64.DsaGenerator
open VG VG.Proof.Dsa.AArch64.Generator

def artifacts (v : Proof.MillerRabin.AArch64.RoundImpl) : List Artifact :=
  ([128, 256, 384] : List Nat).attach.map fun (b : { n : Nat // n ∈ ([128, 256, 384] : List Nat) }) =>
    (Spec.Dsa.GeneratorStage.api (Impl.Dsa.AArch64.Generator.layout b.val)).artifact AArch64.target {
      suffix := v.suffix
      stack := 288
      code := stageCode v b.val
      verified := verified v (Supported.of_mem b.property)
      features := v.features }

end VG.Generic.MillerRabin.AArch64.DsaGenerator
