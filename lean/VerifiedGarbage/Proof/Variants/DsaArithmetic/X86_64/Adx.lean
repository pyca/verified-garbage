module

import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCall
public import VerifiedGarbage.Proof.Variants.DsaArithmetic.X86_64.Checks
public import VerifiedGarbage.Proof.Dsa.X86_64.Slots
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
# BMI2/ADX Montgomery arithmetic for DSA: the variant's code and proofs

The variant `VG.Variants.DsaArithmetic.X86_64.Adx.variant`
(`Variants/DsaArithmetic/X86_64/Adx.lean`), with the proofs its interface asks
for.
-/

@[expose] public section

namespace VG.Proof.Variants.DsaArithmetic.X86_64.Adx

open VG VG.X86_64 VG.Proof.Dsa.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

/-- The tests of the entry points, which the kernel evaluates in one
declaration (`Checks`). -/
theorem checks : Checks MontS.fnLazyAdx.mm Mont.fnAdx.mm :=
  .of_eval (by decide +kernel)

/-- What the kernel evaluates of the functions that call the variant through
slots, and of the complete entry points that call three of them, in one
declaration. -/
theorem slotChecks : Slots.entriesOk Impl.Scrub.X86_64.VecLevel.sse.level "_adx" CallMont.adx.name "vg_rsa_lazy_mont_mul_adx" CallMont.adx.body
    Impl.Bignum.X86_64.MontFn.mulAdxLazy = true := by
  decide +kernel

theorem slotOk : Slots.EntriesOk Impl.Scrub.X86_64.VecLevel.sse.level "_adx" CallMont.adx.name "vg_rsa_lazy_mont_mul_adx" CallMont.adx.body
    Impl.Bignum.X86_64.MontFn.mulAdxLazy :=
  .of_eval slotChecks

def variant : Backend where
  stack := 72
  suffix := "_adx"
  features := ["bmi2", "adx"]
  nm := CallMont.adx.name
  ns := "vg_rsa_lazy_mont_mul_adx"
  bm := CallMont.adx.body
  bs := Impl.Bignum.X86_64.MontFn.mulAdxLazy
  parametersVerified := Slots.parameters_verified Mont.fnAdx MontS.fnLazyAdx slotOk.parameters rfl checks.parameters
  parametersSp := forwardS_spSafe slotOk.parameters.sp
  parametersMx := slotOk.parameters.mx
  parametersDepth := slotOk.parameters.wdepth
  prevalidatedSignVerified := Slots.signer_verified Mont.fnAdx MontS.fnLazyAdx slotOk.sign rfl checks.prevalidatedSign
  prevalidatedSignSp := forwardS_spSafe slotOk.sign.sp
  prevalidatedSignMx := slotOk.sign.mx
  prevalidatedSignDepth := slotOk.sign.wdepth
  deriveCheckedVerified := Slots.deriveChecked_verified Mont.fnAdx MontS.fnLazyAdx slotOk.deriveChecked rfl checks.deriveChecked
  deriveCheckedSp := forwardS_spSafe slotOk.deriveChecked.sp
  deriveCheckedMx := slotOk.deriveChecked.mx
  deriveCheckedDepth := slotOk.deriveChecked.wdepth
  stackBound := by decide
  level := .sse
  stack_eq := rfl

/-- The variant, called through slots. -/
def slotVariant : Slots.SlotBackend where
  backend := variant
  M := Mont.fnAdx
  Sq := MontS.fnLazyAdx
  checks := slotChecks
  validateIn := rfl
  verifyIn := rfl
  validatePrivateIn := rfl
  deriveIn := rfl
  validateMx := checks.validate
  verifyMx := checks.verify
  validatePrivateMx := checks.validatePrivate
  deriveMx := checks.derive

end VG.Proof.Variants.DsaArithmetic.X86_64.Adx
