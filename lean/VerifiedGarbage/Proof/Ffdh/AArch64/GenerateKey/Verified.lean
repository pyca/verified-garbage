module
public import VerifiedGarbage.Impl.Ffdh.AArch64.Domain
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBody
public import VerifiedGarbage.Spec.Ffdh.Contract

import VerifiedGarbage.Proof.Ffdh.AArch64.GenerateKey.CTTail

/-!
# `vg_ffdh_generate_key` on AArch64: verified

Correct (`gk_correct`) and constant time (`gk_constantTime`) against
`gkContract`, which the shared contract implies (`gk_implies`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.GenerateKey

open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.Bignum.AArch64.WindowFive

theorem gk_verified (W : Window) (M : Mont) (S : Selector) :
    Verified target (VG.Impl.Ffdh.AArch64.Domain.GenerateKey.code W.code S.code M.mm)
      (Spec.Ffdh.generateKeyContract abi) :=
  Verified.of_correct (gk_correct W M S) (gk_constantTime W M S) gk_implies

end VG.Proof.Ffdh.AArch64.GenerateKey
