module

public import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Absorb
public import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Squeeze
public import VerifiedGarbage.Proof.Sha3.AArch64.Frame
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Pad

@[expose] public section

namespace VG.Generic.Keccak.AArch64.Stream

/-- Every sponge entry point follows every registered permutation backend. There is no
`vg_keccak_absorb`: the Rust sponge calls `vg_keccak_absorb_scratch` with its working space on
its own stack, rather than a function allocating it on each call. -/
def artifacts (v : Proof.Sha3.AArch64.Permutation) : List Artifact := [
  Spec.Sha3.absorbScratchApi.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    code := Impl.Sha3.AArch64.Stream.absorbWith v.callee
    stack := 16
    verified := (Proof.Sha3.AArch64.Stream.Absorb.absorb_verified v) },
  Spec.Sha3.padApi.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    code := Impl.StackScratch.AArch64.withStackScratch 640 .x4
      (Impl.Sha3.AArch64.Stream.padWith v.callee)
    stack := 656
    verified := Proof.Sha3.AArch64.Frame.pad_framed v },
  Spec.Sha3.squeezeApi.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    code := Impl.StackScratch.AArch64.withStackScratch 640 .x5
      (Impl.Sha3.AArch64.Stream.squeezeWith v.callee)
    stack := 656
    verified := Proof.Sha3.AArch64.Frame.squeeze_framed v }]

end VG.Generic.Keccak.AArch64.Stream
