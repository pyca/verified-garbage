import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Absorb
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Pad
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Squeeze
import VerifiedGarbage.Proof.Sha3.AArch64.Frame

namespace VG.Generic.Keccak.AArch64.Stream

/-- Every sponge entry point follows every registered permutation backend. -/
def artifacts (v : Proof.Sha3.AArch64.Permutation) : List Artifact := [
  { Spec.Sha3.absorbApi with
    name := Spec.Sha3.absorbApi.name ++ v.callee.suffix
    features := v.features
    target := AArch64.target
    doc := Spec.Sha3.absorbApi.doc
    code := Impl.StackScratch.AArch64.withStackScratch 640 .x5
      (Impl.Sha3.AArch64.Stream.absorbWith v.callee)
    contract := Spec.Sha3.absorbContract AArch64.abi 656
    stack := 656
    verified := Proof.Sha3.AArch64.Frame.absorb_framed v
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha3.absorbScratchApi with
    name := Spec.Sha3.absorbScratchApi.name ++ v.callee.suffix
    features := v.features
    target := AArch64.target
    doc := Spec.Sha3.absorbScratchApi.doc
    code := Impl.Sha3.AArch64.Stream.absorbWith v.callee
    contract := Spec.Sha3.absorbScratchContract AArch64.abi 16
    stack := 16
    verified := (Proof.Sha3.AArch64.Stream.Absorb.absorb_verified v)
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha3.padApi with
    name := Spec.Sha3.padApi.name ++ v.callee.suffix
    features := v.features
    target := AArch64.target
    doc := Spec.Sha3.padApi.doc
    code := Impl.StackScratch.AArch64.withStackScratch 640 .x4
      (Impl.Sha3.AArch64.Stream.padWith v.callee)
    contract := Spec.Sha3.padContract AArch64.abi 656
    stack := 656
    verified := Proof.Sha3.AArch64.Frame.pad_framed v
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha3.padScratchApi with
    name := Spec.Sha3.padScratchApi.name ++ v.callee.suffix
    features := v.features
    target := AArch64.target
    doc := Spec.Sha3.padScratchApi.doc
    code := Impl.Sha3.AArch64.Stream.padWith v.callee
    contract := Spec.Sha3.padScratchContract AArch64.abi 16
    stack := 16
    verified := (Proof.Sha3.AArch64.Stream.Pad.pad_verified v)
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha3.squeezeApi with
    name := Spec.Sha3.squeezeApi.name ++ v.callee.suffix
    features := v.features
    target := AArch64.target
    doc := Spec.Sha3.squeezeApi.doc
    code := Impl.StackScratch.AArch64.withStackScratch 640 .x5
      (Impl.Sha3.AArch64.Stream.squeezeWith v.callee)
    contract := Spec.Sha3.squeezeContract AArch64.abi 656
    stack := 656
    verified := Proof.Sha3.AArch64.Frame.squeeze_framed v
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha3.squeezeScratchApi with
    name := Spec.Sha3.squeezeScratchApi.name ++ v.callee.suffix
    features := v.features
    target := AArch64.target
    doc := Spec.Sha3.squeezeScratchApi.doc
    code := Impl.Sha3.AArch64.Stream.squeezeWith v.callee
    contract := Spec.Sha3.squeezeScratchContract AArch64.abi 16
    stack := 16
    verified := (Proof.Sha3.AArch64.Stream.Squeeze.squeeze_verified v)
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Generic.Keccak.AArch64.Stream
