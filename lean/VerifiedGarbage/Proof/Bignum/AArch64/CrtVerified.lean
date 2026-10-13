module

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTCode
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTNSetup
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtImplies
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# `vg_rsa_private_crt` on AArch64: verified against the shared contract

`n`'s setup (`nSetup_ct`) and `main`'s other parts are constant time, so the
function is (`crtCode_constantTime`); with correctness (`crtCode_correct`)
and the contract on the registers and the stack (`crt_implies`), `code` is
verified (`crt_verified`).
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Rsa.AArch64 (crtA)

/-- `vg_rsa_private_crt` is constant time. -/
theorem crtCode_constantTime (M : Mont) : ConstantTime isa crtA.pre crtA.pub (code M.mm) :=
  crtCode_constantTime_of_setup M (nSetup_ct M)

/-- `vg_rsa_private_crt` with Montgomery multiplication `M`. -/
theorem crt_verified (M : Mont) : Verified AArch64.target (code M.mm) (Spec.Rsa.privateCrtContract abi 0) :=
  Verified.of_correct (crtCode_correct M) (crtCode_constantTime M) crt_implies

end VG.Proof.Bignum.AArch64
