module
public import VerifiedGarbage.Impl.Ffdh.AArch64.Domain
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBody
public import VerifiedGarbage.Spec.Ffdh.Contract

import VerifiedGarbage.Proof.Ffdh.AArch64.Exchange.CT

/-!
# `vg_ffdh_exchange` on AArch64: verified

Correct (`ex_correct`) and constant time (`ex_constantTime`) against
`exContract`, which the shared contract implies (`ex_implies`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Exchange

open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.Bignum.AArch64.WindowFive

theorem ex_verified (W : Window) (M : Mont) (S : Selector) :
    Verified target (VG.Impl.Ffdh.AArch64.Domain.Exchange.code W.code S.code M.mm)
      (Spec.Ffdh.exchangeContract abi) :=
  Verified.of_correct (ex_correct W M S) (ex_constantTime W M S) ex_implies

end VG.Proof.Ffdh.AArch64.Exchange
