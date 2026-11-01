module
public import VerifiedGarbage.Proof.Weierstrass.Arm.MontContract

import VerifiedGarbage.Proof.Weierstrass.Arm.MontUmaal
meta import VerifiedGarbage.Proof.Weierstrass.Arm.MontUmaal

import VerifiedGarbage.Proof.Weierstrass.Arm.MontVerified
import VerifiedGarbage.Proof.Weierstrass.Arm.MontBrainpoolP384r1
import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Weierstrass.Arm.MontContract
meta import VerifiedGarbage.Proof.Weierstrass.Arm.MontVerified
meta import VerifiedGarbage.Proof.Weierstrass.Arm.MontBrainpoolP384r1
meta import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# Montgomery multiplication modulo brainpoolP384r1's `p` and `n` with `umaal`, on 32-bit ARM: verified

`vg_brainpoolp384r1_mul_mod_p_umaal` and `vg_brainpoolp384r1_mul_mod_n_umaal` (`mulFnU`) meet the
contract of `vg_brainpoolp384r1_mul_mod_p` and `vg_brainpoolp384r1_mul_mod_n`: the proof against
`mulArm` (`mulU_verified`, `MontUmaal.lean`), and constant time
by taint tracking with `umaal` (`taintU`). Apart from the other curves', so
that adding them rebuilds none of their proofs.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.Arm.Mont

open VG VG.Arm VG.Impl.Weierstrass.Arm.Mont Impl.Weierstrass.Mont

theorem brainpoolp384r1p_mulU_ct : ConstantTime isa (mulArm brainpoolp384r1p).pre (mulArm brainpoolp384r1p).pub (mulFnU brainpoolp384r1p.k brainpoolp384r1p.m) :=
  VG.Taint.constantTime (A := taintU) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (armPub_agree hp)) (by taint_decide)

theorem brainpoolp384r1p_mulU_verified : Verified Arm.target (mulFnU brainpoolp384r1p.k brainpoolp384r1p.m) (brainpoolp384r1p.mulContract Arm.abi) :=
  mulU_verified brainpoolp384r1p brainpoolp384r1p_ok (by decide) brainpoolp384r1p_mulU_ct

theorem brainpoolp384r1n_mulU_ct : ConstantTime isa (mulArm brainpoolp384r1n).pre (mulArm brainpoolp384r1n).pub (mulFnU brainpoolp384r1n.k brainpoolp384r1n.m) :=
  VG.Taint.constantTime (A := taintU) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (armPub_agree hp)) (by taint_decide)

theorem brainpoolp384r1n_mulU_verified : Verified Arm.target (mulFnU brainpoolp384r1n.k brainpoolp384r1n.m) (brainpoolp384r1n.mulContract Arm.abi) :=
  mulU_verified brainpoolp384r1n brainpoolp384r1n_ok (by decide) brainpoolp384r1n_mulU_ct

end VG.Proof.Weierstrass.Arm.Mont
