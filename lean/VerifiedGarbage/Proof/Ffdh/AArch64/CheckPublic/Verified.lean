module

public import VerifiedGarbage.Proof.Ffdh.AArch64.CheckPublic.CT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Spec.Dsa.SignVerify

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
