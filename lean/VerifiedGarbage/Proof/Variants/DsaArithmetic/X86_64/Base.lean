module

public import VerifiedGarbage.Proof.Dsa.X86_64.Backend
import VerifiedGarbage.Proof.Dsa.X86_64.Calls
import VerifiedGarbage.Proof.Dsa.X86_64.KeygenCalls
public import VerifiedGarbage.Proof.Bignum.X86_64.MontSqFn
public import VerifiedGarbage.Proof.Rsa.X86_64.CallMont

/-!
# Baseline x86-64 Montgomery arithmetic for DSA: the variant's code and proofs

The variant `VG.Variants.DsaArithmetic.X86_64.Base.variant`
(`Variants/DsaArithmetic/X86_64/Base.lean`), with the proofs its interface
asks for.
-/

@[expose] public section

namespace VG.Proof.Variants.DsaArithmetic.X86_64.Base

open VG VG.X86_64 VG.Proof.Dsa.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

def variant : Backend where
  sq := CallMont.lazyBase
  mul := CallMont.base.mm
  stack := 8
  suffix := ""
  features := []
  signVerified := signing_call_verified Mont.fnBase MontS.fnLazy (by decide +kernel) rfl (by decide +kernel)
  verifyVerified := verifying_call_verified Mont.fnBase MontS.fnLazy (by decide +kernel) rfl (by decide +kernel)
  signSp := Code.all_of_allInstrs (by decide +kernel)
  verifySp := Code.all_of_allInstrs (by decide +kernel)
  signDepth := by decide +kernel
  parametersVerified := parameters_call_verified Mont.fnBase MontS.fnLazy (by decide +kernel) rfl (by decide +kernel)
  deriveVerified := derive_call_verified Mont.fnBase MontS.fnLazy (by decide +kernel) rfl (by decide +kernel)
  parametersSp := Code.all_of_allInstrs (by decide +kernel)
  deriveSp := Code.all_of_allInstrs (by decide +kernel)
  parametersDepth := by decide +kernel
  deriveDepth := by decide +kernel
  stackBound := by decide

end VG.Proof.Variants.DsaArithmetic.X86_64.Base
