import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTCode
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTNSetup
import VerifiedGarbage.Proof.Bignum.AArch64.CrtImplies

/-!
# `vg_rsa_private_crt` on AArch64: verified against the shared contract

`n`'s setup (`nSetup_ct`) and `main`'s other parts are constant time, so the
function is (`crtCode_constantTime`); with correctness (`crtCode_correct`)
and the contract on the registers and the stack (`crt_implies`), `code` is
verified (`crt_verified`).
-/

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
