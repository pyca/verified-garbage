module

public import VerifiedGarbage.Proof.Ffdh.AArch64.CheckDomain.CT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Spec.Dsa.SignVerify

/-!
# `vg_ffdh_check_domain` on AArch64: verified

Correct (`cd_correct`) and constant time (`cd_constantTime`) against
`cdContract`, which the shared contract implies (`cd_implies`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.CheckDomain

open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.Bignum.AArch64.WindowFive

theorem cd_verified (W : Window) (M : Mont) (S : Selector) :
    Verified target (VG.Impl.Ffdh.AArch64.Domain.CheckDomain.code W.code S.code M.mm)
      (Spec.Ffdh.checkDomainContract abi) :=
  Verified.of_correct (cd_correct W M S) (cd_constantTime W M S) cd_implies

end VG.Proof.Ffdh.AArch64.CheckDomain
