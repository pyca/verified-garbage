module

public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCall
public import VerifiedGarbage.Proof.Variants.DsaArithmetic.X86_64.Checks
public import VerifiedGarbage.Proof.Dsa.X86_64.PrevalidatedSignVerified
public import VerifiedGarbage.Proof.Dsa.X86_64.DeriveCheckedVerified
public import VerifiedGarbage.Proof.Bignum.X86_64.MontSqFn
public import VerifiedGarbage.Proof.Rsa.X86_64.CallMont
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Dsa.X86_64.PublicKeyCT
import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingCT
import VerifiedGarbage.Proof.MdStream.Spec
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledMontCT
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxDualAddClose
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxHeaderSave
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8Row
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareChoice
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareBackend
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Redc
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Memory
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8ProductStep
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Core
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareWideRow
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareRaw
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledMont
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareCross
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledCounter
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRow
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRaw
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledTail
public import VerifiedGarbage.Proof.Bignum.X86_64.CallPost
public import VerifiedGarbage.Proof.Dsa.X86_64.PrevalidatedVerified
public import VerifiedGarbage.Proof.Dsa.X86_64.ValidatePrivateVerified
public import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
public import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Dsa.X86_64.CheckOperands
import VerifiedGarbage.Proof.Dsa.X86_64.AcceptedSpec
import VerifiedGarbage.Proof.Sha256.Stream
public import VerifiedGarbage.Impl.Bignum.X86_64.AdxSquare
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxStep
public import VerifiedGarbage.Proof.Bignum.X86_64.MontFnVerified
public import VerifiedGarbage.Proof.Bignum.X86_64.MontFnAdxCT

/-!
# Baseline x86-64 Montgomery arithmetic for DSA: the variant's code and proofs

The variant `VG.Variants.DsaArithmetic.X86_64.Base.variant`
(`Variants/DsaArithmetic/X86_64/Base.lean`), with the proofs its interface
asks for.
-/

@[expose] public section

namespace VG.Proof.Variants.DsaArithmetic.X86_64.Base

open VG VG.X86_64 VG.Proof.Dsa.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

/-- The tests of the entry points, which the kernel evaluates in one
declaration (`Checks`). -/
theorem checks : Checks CallMont.lazyBase CallMont.base.mm MontS.fnLazy.mm Mont.fnBase.mm 8 :=
  .of_eval (by decide +kernel)

def variant : Backend where
  sq := CallMont.lazyBase
  mul := CallMont.base.mm
  stack := 8
  suffix := ""
  features := []
  signVerified := signing_call_verified Mont.fnBase MontS.fnLazy checks.sign.inl rfl checks.sign.mx
  signSp := checks.sign.sp
  signMx := checks.sign.mxFree
  validateVerified := validating_call_verified Mont.fnBase MontS.fnLazy checks.validate.inl rfl checks.validate.mx
  prevalidatedVerified := prevalidated_call_verified Mont.fnBase MontS.fnLazy checks.verify.inl rfl checks.verify.mx
  validateSp := checks.validate.sp
  prevalidatedSp := checks.verify.sp
  signDepth := checks.sign.depth
  parametersVerified := parameters_call_verified Mont.fnBase MontS.fnLazy checks.parameters.inl rfl checks.parameters.mx
  deriveVerified := derive_call_verified Mont.fnBase MontS.fnLazy checks.derive.inl rfl checks.derive.mx
  parametersSp := checks.parameters.sp
  parametersMx := checks.parameters.mxFree
  deriveSp := checks.derive.sp
  parametersDepth := checks.parameters.depth
  deriveDepth := checks.derive.depth
  prevalidatedSignVerified := prevalidated_sign_call_verified Mont.fnBase MontS.fnLazy checks.prevalidatedSign.inl rfl checks.prevalidatedSign.mx
  prevalidatedSignSp := checks.prevalidatedSign.sp
  prevalidatedSignMx := checks.prevalidatedSign.mxFree
  prevalidatedSignDepth := checks.prevalidatedSign.depth
  validatePrivateVerified := validating_private_call_verified Mont.fnBase MontS.fnLazy checks.validatePrivate.inl rfl checks.validatePrivate.mx
  validatePrivateSp := checks.validatePrivate.sp
  deriveCheckedVerified := derive_checked_call_verified Mont.fnBase MontS.fnLazy checks.deriveChecked.inl rfl checks.deriveChecked.mx
  deriveCheckedSp := checks.deriveChecked.sp
  deriveCheckedMx := checks.deriveChecked.mxFree
  deriveCheckedDepth := checks.deriveChecked.depth
  stackBound := by decide

end VG.Proof.Variants.DsaArithmetic.X86_64.Base
