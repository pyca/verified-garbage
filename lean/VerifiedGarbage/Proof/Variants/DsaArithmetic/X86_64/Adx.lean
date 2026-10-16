module

public import VerifiedGarbage.Proof.Dsa.X86_64.Backend
public import VerifiedGarbage.Proof.Dsa.X86_64.Calls
public import VerifiedGarbage.Proof.Bignum.X86_64.MontSqFn
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Dsa.X86_64.EqualCT
import VerifiedGarbage.Proof.Dsa.X86_64.JointCallCT
import VerifiedGarbage.Proof.Dsa.X86_64.ReadyMinusCT
import VerifiedGarbage.Proof.Dsa.X86_64.ReadyRangeCT
import VerifiedGarbage.Proof.Dsa.X86_64.ZeroCT
import VerifiedGarbage.Proof.MdStream.Spec

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
  stackBound := by decide

end VG.Proof.Variants.DsaArithmetic.X86_64.Adx
