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
      notes := ["Parameter generation's generator search and domain check on p, q and the exponent at \
        their offsets of the generation's scratch space, with the arithmetic of the round's \
        implementation. Its 272-byte frame holds the stage's arguments in the slots where the \
        generation keeps them; the callee-saved registers are saved in the scratch space's control \
        area. Its contract asks for 288 bytes of stack: the frame and the 16 bytes below it, which \
        the generation's frame layout keeps apart."]
      stack := 288
      code := stageCode v b.val
      verified := verified v (Supported.of_mem b.property)
      features := v.features }

end VG.Generic.MillerRabin.AArch64.DsaGenerator
