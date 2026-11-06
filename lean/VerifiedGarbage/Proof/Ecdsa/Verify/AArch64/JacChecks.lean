module

import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.CT
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacPrefix
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacCombTiming
public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Jacobian
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.CT
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacPrefix
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.JacCombTiming
meta import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Jacobian
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot
import VerifiedGarbage.Proof.Framework.AArch64.Inline
meta import VerifiedGarbage.Proof.Framework.AArch64.Inline

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Weierstrass.AArch64
open VG.Impl.Weierstrass.AArch64

tactic_template "jac_field_ct" : tactic => `(tactic|
  exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.x0])
    (fun _ _ _ _ h => h) (by taint_decide))

tactic_template "jac_reg_ct" rs:term : tactic => `(tactic|
  exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs $rs)
    (fun _ _ _ _ h => h) (by taint_decide))

end VG.Proof.Ecdsa.Verify.AArch64
