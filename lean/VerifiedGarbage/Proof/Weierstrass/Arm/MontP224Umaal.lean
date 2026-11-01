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
# Montgomery multiplication modulo P-224's `p` and `n` with `umaal`, on 32-bit ARM: verified

`vg_p224_mul_mod_p_umaal` and `vg_p224_mul_mod_n_umaal` (`mulFnU`) meet the
contract of `vg_p224_mul_mod_p` and `vg_p224_mul_mod_n`: the proof against
`mulArm` (`mulU_verified`, `MontUmaal.lean`), and constant time
by taint tracking with `umaal` (`taintU`). Apart from the other curves', so
that adding them rebuilds none of their proofs.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.Arm.Mont

open VG VG.Arm VG.Impl.Weierstrass.Arm.Mont Impl.Weierstrass.Mont

theorem p224p_mulU_ct : ConstantTime isa (mulArm p224p).pre (mulArm p224p).pub (mulFnU p224p.k p224p.m) :=
  VG.Taint.constantTime (A := taintU) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (armPub_agree hp)) (by taint_decide)

theorem p224p_mulU_verified : Verified Arm.target (mulFnU p224p.k p224p.m) (p224p.mulContract Arm.abi) :=
  mulU_verified p224p p224p_ok (by decide) p224p_mulU_ct

theorem p224n_mulU_ct : ConstantTime isa (mulArm p224n).pre (mulArm p224n).pub (mulFnU p224n.k p224n.m) :=
  VG.Taint.constantTime (A := taintU) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (armPub_agree hp)) (by taint_decide)

theorem p224n_mulU_verified : Verified Arm.target (mulFnU p224n.k p224n.m) (p224n.mulContract Arm.abi) :=
  mulU_verified p224n p224n_ok (by decide) p224n_mulU_ct

end VG.Proof.Weierstrass.Arm.Mont
