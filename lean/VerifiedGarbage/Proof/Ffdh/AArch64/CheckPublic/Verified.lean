module
public import VerifiedGarbage.Impl.Ffdh.AArch64.Domain
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBody
public import VerifiedGarbage.Spec.Ffdh.Contract

import VerifiedGarbage.Proof.Ffdh.AArch64.CheckPublic.CT
import VerifiedGarbage.Proof.Ffdh.AArch64.CheckPublic.Correct

/-!
# `vg_ffdh_check_public` on AArch64: verified

Correct (`cp_correct`) and constant time (`cp_constantTime`) against
`cpContract`, which the shared contract implies (`cp_implies`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.CheckPublic

open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.Bignum.AArch64.WindowFive

theorem cp_verified (W : Window) (M : Mont) (S : Selector) :
    Verified target (VG.Impl.Ffdh.AArch64.Domain.CheckPublic.code W.code S.code M.mm)
      (Spec.Ffdh.checkPublicContract abi) :=
  Verified.of_correct (cp_correct W M S) (cp_constantTime W M S) cp_implies

end VG.Proof.Ffdh.AArch64.CheckPublic
