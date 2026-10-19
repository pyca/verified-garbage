module

public import VerifiedGarbage.Proof.Dsa.X86_64.Backend
import VerifiedGarbage.Proof.Dsa.X86_64.Calls
import VerifiedGarbage.Proof.Dsa.X86_64.KeygenCalls
public import VerifiedGarbage.Proof.Bignum.X86_64.MontSqFn
public import VerifiedGarbage.Proof.Rsa.X86_64.CallMont

/-!
# BMI2/ADX Montgomery arithmetic for DSA: the variant's code and proofs

The variant `VG.Variants.DsaArithmetic.X86_64.Adx.variant`
(`Variants/DsaArithmetic/X86_64/Adx.lean`), with the proofs its interface asks
for.
-/

@[expose] public section

namespace VG.Proof.Variants.DsaArithmetic.X86_64.Adx

open VG VG.X86_64 VG.Proof.Dsa.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

def variant : Backend where
  sq := CallMont.lazyAdx
  mul := CallMont.adx.mm
  stack := 8
  suffix := "_adx"
  features := ["bmi2", "adx"]
  signVerified := signing_call_verified Mont.fnAdx MontS.fnLazyAdx (by decide +kernel) rfl (by decide +kernel)
  verifyVerified := verifying_call_verified Mont.fnAdx MontS.fnLazyAdx (by decide +kernel) rfl (by decide +kernel)
  signSp := Code.all_of_allInstrs (by decide +kernel)
  verifySp := Code.all_of_allInstrs (by decide +kernel)
  signDepth := by decide +kernel
  parametersVerified := parameters_call_verified Mont.fnAdx MontS.fnLazyAdx (by decide +kernel) rfl (by decide +kernel)
  deriveVerified := derive_call_verified Mont.fnAdx MontS.fnLazyAdx (by decide +kernel) rfl (by decide +kernel)
  parametersSp := Code.all_of_allInstrs (by decide +kernel)
  deriveSp := Code.all_of_allInstrs (by decide +kernel)
  parametersDepth := by decide +kernel
  deriveDepth := by decide +kernel
  stackBound := by decide

end VG.Proof.Variants.DsaArithmetic.X86_64.Adx
