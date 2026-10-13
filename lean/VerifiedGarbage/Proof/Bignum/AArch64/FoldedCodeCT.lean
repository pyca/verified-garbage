module

public import VerifiedGarbage.Proof.Bignum.AArch64.FoldedRestCT
public import VerifiedGarbage.Proof.Bignum.AArch64.PdCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

@[expose] public section
namespace VG.Proof.Bignum.AArch64.FoldedPublic
open VG VG.AArch64 VG.Impl.Rsa.AArch64

theorem code_constantTime (M : Mont) :
    ConstantTime isa pdContract.pre pdContract.pub (Folded.code M.mm) :=
  pdCodeWith_constantTime (Folded.code M.mm) (pdCodeWith_ct (Folded.rest M.mm) (rest_ct M))

end VG.Proof.Bignum.AArch64.FoldedPublic
