module
public import VerifiedGarbage.Impl.Ffdh.AArch64.Derive
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBody
public import VerifiedGarbage.Spec.Ffdh.DerivePublicContract

import VerifiedGarbage.Proof.Ffdh.AArch64.Derive.CT

/-!
# `vg_ffdh_derive_public` on AArch64: verified

Correct (`dv_correct`) and constant time (`dv_constantTime`) against
`dvContract`, which the shared contract implies (`dv_implies`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Derive

open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.Bignum.AArch64.WindowFive

theorem dv_verified (W : Window) (M : Mont) (S : Selector) :
    Verified target (VG.Impl.Ffdh.AArch64.Domain.DerivePublic.code W.code S.code M.mm)
      (Spec.Ffdh.derivePublicContract abi) :=
  Verified.of_correct (dv_correct W M S) (dv_constantTime W M S) dv_implies

end VG.Proof.Ffdh.AArch64.Derive
