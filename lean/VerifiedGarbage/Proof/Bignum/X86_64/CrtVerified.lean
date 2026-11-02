module
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtContract

import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTCode
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTFin
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTQ
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTP
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRedc
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetup
import VerifiedGarbage.Proof.Bignum.X86_64.CrtImplies
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTGPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Rsa.Contract
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtContract
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTCode
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTFin
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTQ
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTP
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRedc
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetup
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtImplies
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTGPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Rsa.Contract

/-!
# `vg_rsa_private_crt` on x86-64: verified against the shared contract

`main`'s parts are constant time (`setup_ct`, `checks_ct`, the phases from
`G`, `redc` and the exponentiation, `crtFinish_ct`), so the function is
(`crtCode_constantTime`); with correctness (`crtCode_correct`) and the
contract on the registers and the stack (`crt_implies`), `Crt.code` is
verified (`crt_verified`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt

/-- `vg_rsa_private_crt` is constant time but for `n`. -/
theorem crtCode_constantTime (M : Mont) (E : CrtExpL M) (hE : E.CT) : ConstantTime isa crtContract.pre crtContract.pub (Crt.code M.mm E.code) :=
  crtCode_constantTime_of M E setup_ct checks_ct
    (qPhase_ct M E (unit_ct M (gPow_ct_Q M) (redc_ct_Y M) (by taint_decide))
      (pow_ct M E (redc_ct_Y M) hE.2 (by taint_decide)))
    (pPhase_ct M E (unit_ct M (gPow_ct_P M) (redc_ct_Y M) (by taint_decide))
      (pow_ct M E (redc_ct_Y M) hE.1 (by taint_decide)) (redc_ct_X M) loadArr_ct_pI)
    crtFinish_ct

/-- `vg_rsa_private_crt` with Montgomery multiplication `M`, given that its
code never loads MXCSR (which the registration file evaluates). -/
theorem crt_verified (M : Mont) (E : CrtExpL M) (hE : E.CT) (hmx : (Crt.code M.mm E.code).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target (Crt.code M.mm E.code) (Proof.Rsa.privateCrtContract abi) :=
  Verified.of_correct (crtCode_correct M E hmx) (crtCode_constantTime M E hE) crt_implies

end VG.Proof.Bignum.X86_64
