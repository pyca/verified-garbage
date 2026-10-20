module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourVerified
public import VerifiedGarbage.Proof.Framework.Registration

@[expose] public section

namespace VG.Artifacts.MlDsaBoundedFour.AArch64

def artifact (sha3 : Bool) (η : Nat) (hη : η=2∨η=4) : Artifact :=
 (Spec.MlDsa.rejBoundedFourApi η).artifact AArch64.target {
   suffix := if sha3 then "_sha3" else ""
   features := if sha3 then ["sha3"] else []
   code := Impl.MlDsa.AArch64.Optimized.BoundedFour.sampler sha3 true η
   verified := Proof.MlDsa.AArch64.Optimized.BoundedFour.sampler_verified sha3 hη }

def artifacts : List Artifact :=
 [artifact false 2 (Or.inl rfl),artifact true 2 (Or.inl rfl),
  artifact false 4 (Or.inr rfl),artifact true 4 (Or.inr rfl)]

end VG.Artifacts.MlDsaBoundedFour.AArch64
