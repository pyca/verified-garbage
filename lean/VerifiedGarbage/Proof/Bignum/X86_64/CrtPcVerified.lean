module

public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTCodePc
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTCodePc
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtPcImplies
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtPcImplies
import VerifiedGarbage.Proof.Bignum.X86_64.CrtVerified
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtVerified
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRedc
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRedc
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExpL
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExpL
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetup
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetup
import VerifiedGarbage.Proof.Framework.X86_64.Call
meta import VerifiedGarbage.Proof.Framework.X86_64.Call

/-!
# `vg_rsa_private_crt_precomputed` on x86-64: verified against the shared contract

`main`'s parts are constant time with `pre` (`qPhasePc_ct`, `pPhasePc_ct`,
and the parts it shares with `vg_rsa_private_crt`), so the function is
(`crtPcCode_constantTime`); with correctness (`crtPcCode_correct`) and the
contract on the registers and the stack (`crtPc_implies`), `Crt.code` with
`pc` is verified (`crtPc_verified`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt

/-- `vg_rsa_private_crt_precomputed` is constant time but for `n`. -/
theorem crtPcCode_constantTime (M : Mont) (E : CrtExpL M) (hE : E.CT) :
    ConstantTime isa crtPcContract.pre crtPcContract.pub (Crt.code M.mm E.code true) :=
  crtPcCode_constantTime_of M E setup_ct checks_ct
    (qPhasePc_ct M E (gPow_ct_Q M) (pow_ct M E (redc_ct_Y M) hE.2 (by taint_decide)))
    (pPhasePc_ct M E (gPow_ct_P M) (pow_ct M E (redc_ct_Y M) hE.1 (by taint_decide)) (redc_ct_X M) loadArr_ct_pI)

/-- `vg_rsa_private_crt_precomputed` with Montgomery multiplication `M`, given
that its code never loads MXCSR (which the registration file evaluates). -/
theorem crtPc_verified (M : Mont) (E : CrtExpL M) (hE : E.CT)
    (hmx : (Crt.code M.mm E.code true).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target (Crt.code M.mm E.code true) (Spec.Rsa.privateCrtPrecomputedContract abi) :=
  Verified.of_correct (crtPcCode_correct M E hmx) (crtPcCode_constantTime M E hE) crtPc_implies

end VG.Proof.Bignum.X86_64
