module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseVerified
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttOutVerified
public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.NttInv
public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Mul
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.AddSubVerified
public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Ntt
public import VerifiedGarbage.Proof.Framework.Registration

/-! # ML-DSA (FIPS 204) on AArch64: the arithmetic of polynomials -/

@[expose] public section

namespace VG.Artifacts.MlDsaArith.AArch64

def artifacts : List Artifact := [
  Spec.MlDsa.montgomeryNttInvApi.artifact AArch64.target {
    consts := Impl.MlDsa.AArch64.Optimized.Inverse.inverseConsts
    code := Impl.MlDsa.AArch64.Optimized.Inverse.staticCode
    verified := Proof.MlDsa.AArch64.Optimized.Inverse.inverse_verified },
  Spec.MlDsa.positiveNttApi.artifact AArch64.target {
    consts := Impl.MlDsa.AArch64.Optimized.Ntt.nttConsts
    code := Impl.MlDsa.AArch64.Optimized.Ntt.staticNtt
    verified := Proof.MlDsa.AArch64.Optimized.positiveNtt_verified },
  Spec.MlDsa.positiveNttOutApi.artifact AArch64.target {
    consts := Impl.MlDsa.AArch64.Optimized.Ntt.nttConsts
    code := Impl.MlDsa.AArch64.Optimized.Ntt.outNtt
    verified := Proof.MlDsa.AArch64.Optimized.positiveNttOut_verified },
  Spec.MlDsa.nttApi.artifact AArch64.target {
    notes := ["Four butterflies per NEON vector; the 256 Montgomery zetas are stored in `scratch`."]
    code := Impl.MlDsa.AArch64.Arith.Neon.ntt
    verified := Proof.MlDsa.AArch64.Arith.Neon.ntt_verified },
  Spec.MlDsa.nttInvApi.artifact AArch64.target {
    notes := ["Four butterflies per NEON vector; the 256 negated Montgomery zetas are stored in `scratch`."]
    code := Impl.MlDsa.AArch64.Arith.Neon.nttInv
    verified := Proof.MlDsa.AArch64.Arith.Neon.nttInv_verified },
  Spec.MlDsa.mulApi.artifact AArch64.target {
    code := Impl.MlDsa.AArch64.Arith.mul
    verified := Proof.MlDsa.AArch64.Arith.mul_verified },
  Spec.MlDsa.mulAddApi.artifact AArch64.target {
    code := Impl.MlDsa.AArch64.Arith.mulAdd
    verified := Proof.MlDsa.AArch64.Arith.mulAdd_verified },
  Spec.MlDsa.addApi.artifact AArch64.target {
    code := Impl.MlDsa.AArch64.Optimized.AddSub.code false
    verified := Proof.MlDsa.AArch64.Optimized.AddSub.add_verified },
  Spec.MlDsa.subApi.artifact AArch64.target {
    code := Impl.MlDsa.AArch64.Optimized.AddSub.code true
    verified := Proof.MlDsa.AArch64.Optimized.AddSub.sub_verified }]

end VG.Artifacts.MlDsaArith.AArch64
