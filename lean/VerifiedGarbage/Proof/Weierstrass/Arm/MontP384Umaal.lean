module
public import VerifiedGarbage.Proof.Weierstrass.Arm.MontContract

import VerifiedGarbage.Proof.Weierstrass.Arm.MontUmaal
meta import VerifiedGarbage.Proof.Weierstrass.Arm.MontUmaal

import VerifiedGarbage.Proof.Weierstrass.Arm.MontVerified
import VerifiedGarbage.Proof.Weierstrass.Arm.MontModuli
import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Weierstrass.Arm.MontContract
meta import VerifiedGarbage.Proof.Weierstrass.Arm.MontVerified
meta import VerifiedGarbage.Proof.Weierstrass.Arm.MontModuli
meta import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# Montgomery multiplication modulo P-384's `p` and `n` with `umaal`, on 32-bit ARM: verified

`vg_p384_mul_mod_p_umaal` and `vg_p384_mul_mod_n_umaal` (`mulFnU`) meet the
contract of `vg_p384_mul_mod_p` and `vg_p384_mul_mod_n`: the proof against
`mulArm` (`mulU_verified`, `MontUmaal.lean`), and constant time
by taint tracking with `umaal` (`taintU`). Apart from the other curves', so
that adding them rebuilds none of their proofs.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.Arm.Mont

open VG VG.Arm VG.Impl.Weierstrass.Arm.Mont Impl.Weierstrass.Mont

theorem p384p_mulU_ct : ConstantTime isa (mulArm p384p).pre (mulArm p384p).pub (mulFnU p384p.k p384p.m) :=
  VG.Taint.constantTime (A := taintU) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (armPub_agree hp)) (by taint_decide)

theorem p384p_mulU_verified : Verified Arm.target (mulFnU p384p.k p384p.m) (p384p.mulContract Arm.abi) :=
  mulU_verified p384p p384p_ok (by decide) p384p_mulU_ct

theorem p384n_mulU_ct : ConstantTime isa (mulArm p384n).pre (mulArm p384n).pub (mulFnU p384n.k p384n.m) :=
  VG.Taint.constantTime (A := taintU) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (armPub_agree hp)) (by taint_decide)

theorem p384n_mulU_verified : Verified Arm.target (mulFnU p384n.k p384n.m) (p384n.mulContract Arm.abi) :=
  mulU_verified p384n p384n_ok (by decide) p384n_mulU_ct

end VG.Proof.Weierstrass.Arm.Mont
