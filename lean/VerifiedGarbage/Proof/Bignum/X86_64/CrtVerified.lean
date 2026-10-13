module

public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTCode
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTCode
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTFin
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTFin
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTQ
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTQ
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTP
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTP
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRedc
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRedc
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetup
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetup
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtImplies
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtImplies
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.X86_64.Call
meta import VerifiedGarbage.Proof.Framework.X86_64.Call

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
theorem crtCode_constantTime (M : Mont) (S : CrtSel) (hS : S.CT) : ConstantTime isa crtContract.pre crtContract.pub (Crt.code M.mm S.code) :=
  crtCode_constantTime_of M S setup_ct checks_ct
    (qPhase_ct M S (unit_ct M (gPow_ct_Q M) (redc_ct_Y M) (by taint_decide))
      (pow_ct M S (redc_ct_Y M) (expLoop_ct_Q M S hS) (by taint_decide)))
    (pPhase_ct M S (unit_ct M (gPow_ct_P M) (redc_ct_Y M) (by taint_decide))
      (pow_ct M S (redc_ct_Y M) (expLoop_ct_P M S hS) (by taint_decide)) (redc_ct_X M) loadArr_ct_pI)
    crtFinish_ct

/-- `vg_rsa_private_crt` with Montgomery multiplication `M`, given that its
code never loads MXCSR (which the registration file evaluates). -/
theorem crt_verified (M : Mont) (S : CrtSel) (hS : S.CT) (hmx : (Crt.code M.mm S.code).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target (Crt.code M.mm S.code) (Spec.Rsa.privateCrtContract abi) :=
  Verified.of_correct (crtCode_correct M S hmx) (crtCode_constantTime M S hS) crt_implies

end VG.Proof.Bignum.X86_64
