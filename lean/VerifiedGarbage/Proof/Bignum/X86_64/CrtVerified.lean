import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTCode
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTFin
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTQ
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTP
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRedc
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupChk
import VerifiedGarbage.Proof.Bignum.X86_64.CrtImplies

/-!
# `vg_rsa_private_crt` on x86-64: verified against the shared contract

`main`'s parts are constant time (`setup_ct`, `checks_ct`, the phases from
`G`, `redc` and the exponentiation, `finish_ct`), so the function is
(`crtCode_constantTime`); with correctness (`crtCode_correct`) and the
contract on the registers and the stack (`crt_implies`), `Crt.code` is
verified (`crt_verified`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt

/-- `vg_rsa_private_crt` is constant time but for `n`. -/
theorem crtCode_constantTime (M : Mont) : ConstantTime isa crtContract.pre crtContract.pub (Crt.code M.mm) :=
  crtCode_constantTime_of M setup_ct checks_ct
    (qPhase_ct M (unit_ct M (gPow_ct_Q M) (redc_ct_Y M) (by taint_decide))
      (pow_ct M (redc_ct_Y M) (expLoop_ct_Q M) (by taint_decide)))
    (pPhase_ct M (unit_ct M (gPow_ct_P M) (redc_ct_Y M) (by taint_decide))
      (pow_ct M (redc_ct_Y M) (expLoop_ct_P M) (by taint_decide)) (redc_ct_X M) loadArr_ct_pI)
    finish_ct

/-- `vg_rsa_private_crt` with Montgomery multiplication `M`, given that its
code never loads MXCSR (which the registration file evaluates). -/
theorem crt_verified (M : Mont) (hmx : (Crt.code M.mm).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target (Crt.code M.mm) (Spec.Rsa.privateCrtContract abi) :=
  Verified.of_correct (crtCode_correct M hmx) (crtCode_constantTime M) crt_implies

end VG.Proof.Bignum.X86_64
