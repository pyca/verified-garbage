module

public import VerifiedGarbage.Proof.Dsa.X86_64.Backend
public import VerifiedGarbage.Proof.Dsa.X86_64.Calls
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Dsa.X86_64.EqualCT
import VerifiedGarbage.Proof.Dsa.X86_64.JointCallCT
import VerifiedGarbage.Proof.Dsa.X86_64.ReadyMinusCT
import VerifiedGarbage.Proof.Dsa.X86_64.ReadyRangeCT
import VerifiedGarbage.Proof.Dsa.X86_64.ZeroCT
import VerifiedGarbage.Proof.MdStream.Spec

/-! # BMI2/ADX Montgomery arithmetic for DSA

Reuse RSA's shared `vg_rsa_mont_mul_adx` kernel, including tiled products
and triangular squaring for aligned widths. Calls avoid duplicating those
kernels at each arithmetic site; their return address uses eight stack bytes.
-/

@[expose] public section

namespace VG.Variants.DsaArithmetic.X86_64.Adx
open VG VG.X86_64 VG.Proof.Dsa.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

def variant : Backend where
  mul := CallMont.adx.mm
  stack := 8
  suffix := "_adx"
  features := ["bmi2", "adx"]
  signVerified := signing_call_verified Mont.fnAdx (by decide +kernel) rfl (by decide +kernel)
  verifyVerified := verifying_call_verified Mont.fnAdx (by decide +kernel) rfl (by decide +kernel)
  signSp := Code.all_of_allInstrs (by decide +kernel)
  verifySp := Code.all_of_allInstrs (by decide +kernel)

end VG.Variants.DsaArithmetic.X86_64.Adx
