module

import VerifiedGarbage.Proof.Bignum.AArch64.FoldedMain
public import VerifiedGarbage.Proof.Bignum.AArch64.PdCode
public import VerifiedGarbage.Impl.Rsa.AArch64.Folded
import VerifiedGarbage.Proof.Framework.Omega

@[expose] public section
namespace VG.Proof.Bignum.AArch64.FoldedPublic
open VG VG.AArch64 VG.Impl.Rsa.AArch64

theorem code_correct (M : Mont) (s : State) (h : pdContract.pre s) :
    ∃ t s', Exec isa (Folded.code M.mm) s t s' ∧ abiPreserved s s' ∧ pdContract.post s s' :=
  pdCodeWith_correct (Folded.rest M.mm) (rest_ok M) s h

end VG.Proof.Bignum.AArch64.FoldedPublic
