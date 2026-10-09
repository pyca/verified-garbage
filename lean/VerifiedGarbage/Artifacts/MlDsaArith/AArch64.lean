import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttOutVerified
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.AddSub
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Mul
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.NttInv

/-! # ML-DSA (FIPS 204) on AArch64: the arithmetic of polynomials -/

namespace VG.Artifacts.MlDsaArith.AArch64

def artifacts : List Artifact := [
  { Spec.MlDsa.montgomeryNttInvApi with
    target := AArch64.target
    doc := Spec.MlDsa.montgomeryNttInvApi.doc
    consts := Impl.MlDsa.AArch64.Optimized.Inverse.inverseConsts
    code := Impl.MlDsa.AArch64.Optimized.Inverse.staticCode
    contract := Spec.MlDsa.montgomeryNttInvContract (AArch64.abi.withConsts Impl.MlDsa.AArch64.Optimized.Inverse.inverseConsts)
    verified := Proof.MlDsa.AArch64.Optimized.Inverse.inverse_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _
    ofSig := ⟨_,_,_,by unfold Spec.MlDsa.montgomeryNttInvContract Spec.MlDsa.inPlaceContract; rfl⟩ },
  { Spec.MlDsa.positiveNttApi with
    target := AArch64.target
    doc := Spec.MlDsa.positiveNttApi.doc
    consts := Impl.MlDsa.AArch64.Optimized.Ntt.nttConsts
    code := Impl.MlDsa.AArch64.Optimized.Ntt.staticNtt
    contract := Spec.MlDsa.positiveNttContract (AArch64.abi.withConsts Impl.MlDsa.AArch64.Optimized.Ntt.nttConsts)
    verified := Proof.MlDsa.AArch64.Optimized.positiveNtt_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.positiveNttOutApi with
    target := AArch64.target
    doc := Spec.MlDsa.positiveNttOutApi.doc
    consts := Impl.MlDsa.AArch64.Optimized.Ntt.nttConsts
    code := Impl.MlDsa.AArch64.Optimized.Ntt.outNtt
    contract := Spec.MlDsa.positiveNttOutContract (AArch64.abi.withConsts Impl.MlDsa.AArch64.Optimized.Ntt.nttConsts)
    verified := Proof.MlDsa.AArch64.Optimized.positiveNttOut_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.nttApi with
    target := AArch64.target
    doc := Spec.MlDsa.nttApi.doc
      (notes := ["Four butterflies per NEON vector; the 256 Montgomery zetas are stored in `scratch`."])
    code := Impl.MlDsa.AArch64.Arith.Neon.ntt
    contract := Spec.MlDsa.nttContract AArch64.abi
    verified := Proof.MlDsa.AArch64.Arith.Neon.ntt_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _
    ofSig := ⟨_, _, _, by unfold Spec.MlDsa.nttContract Spec.MlDsa.inPlaceContract; rfl⟩ },
  { Spec.MlDsa.nttInvApi with
    target := AArch64.target
    doc := Spec.MlDsa.nttInvApi.doc
      (notes := ["Four butterflies per NEON vector; the 256 negated Montgomery zetas are stored in `scratch`."])
    code := Impl.MlDsa.AArch64.Arith.Neon.nttInv
    contract := Spec.MlDsa.nttInvContract AArch64.abi
    verified := Proof.MlDsa.AArch64.Arith.Neon.nttInv_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _
    ofSig := ⟨_, _, _, by unfold Spec.MlDsa.nttInvContract Spec.MlDsa.inPlaceContract; rfl⟩ },
  { Spec.MlDsa.mulApi with
    target := AArch64.target
    doc := Spec.MlDsa.mulApi.doc
    code := Impl.MlDsa.AArch64.Arith.mul
    contract := Spec.MlDsa.mulContract AArch64.abi
    verified := Proof.MlDsa.AArch64.Arith.mul_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.mulAddApi with
    target := AArch64.target
    doc := Spec.MlDsa.mulAddApi.doc
    code := Impl.MlDsa.AArch64.Arith.mulAdd
    contract := Spec.MlDsa.mulAddContract AArch64.abi
    verified := Proof.MlDsa.AArch64.Arith.mulAdd_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.addApi with
    target := AArch64.target
    doc := Spec.MlDsa.addApi.doc
    code := Impl.MlDsa.AArch64.Arith.add
    contract := Spec.MlDsa.addContract AArch64.abi
    verified := Proof.MlDsa.AArch64.Arith.add_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.subApi with
    target := AArch64.target
    doc := Spec.MlDsa.subApi.doc
    code := Impl.MlDsa.AArch64.Arith.sub
    contract := Spec.MlDsa.subContract AArch64.abi
    verified := Proof.MlDsa.AArch64.Arith.sub_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.MlDsaArith.AArch64
