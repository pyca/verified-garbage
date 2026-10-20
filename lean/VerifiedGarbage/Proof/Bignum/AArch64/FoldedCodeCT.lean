module
public import VerifiedGarbage.Impl.Rsa.AArch64.Folded
public import VerifiedGarbage.Proof.Bignum.AArch64.PdCode

import VerifiedGarbage.Proof.Bignum.AArch64.FoldedRestCT
import VerifiedGarbage.Proof.Bignum.AArch64.PdCT
import VerifiedGarbage.Proof.Framework.Omega

@[expose] public section
namespace VG.Proof.Bignum.AArch64.FoldedPublic
open VG VG.AArch64 VG.Impl.Rsa.AArch64

theorem code_constantTime (M : Mont) :
    ConstantTime isa pdContract.pre pdContract.pub (Folded.code M.mm) :=
  pdCodeWith_constantTime (Folded.code M.mm) (pdCodeWith_ct (Folded.rest M.mm) (rest_ct M))

end VG.Proof.Bignum.AArch64.FoldedPublic
