import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourVerified

namespace VG.Artifacts.MlDsaBoundedFour.AArch64

def artifact (sha3 : Bool) (η : Nat) (hη : η=2∨η=4) : Artifact :=
 { Spec.MlDsa.rejBoundedFourApi η with
   name := (Spec.MlDsa.rejBoundedFourApi η).name ++ if sha3 then "_sha3" else ""
   features := if sha3 then ["sha3"] else []
   target := AArch64.target
   doc := (Spec.MlDsa.rejBoundedFourApi η).doc
   code := Impl.MlDsa.AArch64.Optimized.BoundedFour.sampler sha3 true η
   contract := Spec.MlDsa.rejBoundedFourContract AArch64.abi η
   verified := Proof.MlDsa.AArch64.Optimized.BoundedFour.sampler_verified sha3 hη
   spSafe := Code.all_of_forall (fun _=>rfl) _
   ofSig := ⟨_,_,_,by unfold Spec.MlDsa.rejBoundedFourContract; rfl⟩ }

def artifacts : List Artifact :=
 [artifact false 2 (Or.inl rfl),artifact true 2 (Or.inl rfl),
  artifact false 4 (Or.inr rfl),artifact true 4 (Or.inr rfl)]

end VG.Artifacts.MlDsaBoundedFour.AArch64
