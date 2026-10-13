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

/-! # Baseline x86-64 Montgomery arithmetic for DSA

Reuse RSA's shared Montgomery kernel to avoid duplicating it at each
arithmetic site, including the squarings in R² setup.
-/

@[expose] public section

namespace VG.Variants.DsaArithmetic.X86_64.Base
open VG VG.X86_64 VG.Proof.Dsa.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

def variant : Backend where
  mul := CallMont.base.mm
  stack := 8
  suffix := ""
  features := []
  signVerified := signing_call_verified Mont.fnBase (by decide +kernel) rfl (by decide +kernel)
  verifyVerified := verifying_call_verified Mont.fnBase (by decide +kernel) rfl (by decide +kernel)
  signSp := Code.all_of_allInstrs (by decide +kernel)
  verifySp := Code.all_of_allInstrs (by decide +kernel)

end VG.Variants.DsaArithmetic.X86_64.Base
