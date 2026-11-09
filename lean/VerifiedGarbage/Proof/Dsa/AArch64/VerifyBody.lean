module

public import VerifiedGarbage.Proof.Dsa.AArch64.VerifyBytesSpec
public import VerifiedGarbage.Impl.Dsa.AArch64.SignVerify
import VerifiedGarbage.Proof.Dsa.AArch64.Result
import VerifiedGarbage.Proof.Dsa.SizeBounds

/-! # Verification computation, result return and ABI register restoration -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

structure VerificationOperands (L : ExecutionLayout) (data : VerifyValues) (qb : List Byte) (s : State) : Prop where
  generator : OperandBytes s L.base usedBytes Core.generator data.generator
  publicValue : OperandBytes s L.base usedBytes Core.publicValue data.publicValue
  subgroup : OperandBytes s L.base usedBytes ⟨.input .q, .qLen⟩ qb
  signatureR : OperandBytes s L.base usedBytes Core.signatureR data.signatureR
  signatureS : OperandBytes s L.base usedBytes Core.signatureS data.signatureS
  digest : OperandBytes s L.base usedBytes Core.digest data.digest
  generatorLength : data.generator.length = L.pLen
  publicLength : data.publicValue.length = L.pLen
  subgroupLength : qb.length = L.qLen
  rLength : data.signatureR.length = L.qLen
  sLength : data.signatureS.length = L.qLen
  digestBound : data.digest.length < 2 ^ 64
  subgroupValue : Spec.Dsa.decodeBE qb = L.subgroup

end VG.Proof.Dsa.AArch64
