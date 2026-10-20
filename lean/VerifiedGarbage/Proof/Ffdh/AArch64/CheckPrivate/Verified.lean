module
public import VerifiedGarbage.Impl.Ffdh.AArch64.Domain
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBody
public import VerifiedGarbage.Spec.Ffdh.Contract

import VerifiedGarbage.Proof.Ffdh.AArch64.CheckPrivate.CT

/-!
# `vg_ffdh_check_private` on AArch64: verified

Correct (`kp_correct`) and constant time (`kp_constantTime`) against
`kpContract`, which the shared contract implies (`kp_implies`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.CheckPrivate

open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.Bignum.AArch64.WindowFive

theorem kp_verified (W : Window) (M : Mont) (S : Selector) :
    Verified target (VG.Impl.Ffdh.AArch64.Domain.CheckPrivate.code W.code S.code M.mm)
      (Spec.Ffdh.checkPrivateContract abi) :=
  Verified.of_correct (kp_correct W M S) (kp_constantTime W M S) kp_implies

end VG.Proof.Ffdh.AArch64.CheckPrivate
