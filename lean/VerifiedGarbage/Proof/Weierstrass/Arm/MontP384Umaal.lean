module
public import VerifiedGarbage.Proof.Weierstrass.Arm.MontContract

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
`mulArm` (`mulFnU_ok`, which states what `mulFn_ok` does), and constant time
by taint tracking with `umaal` (`taintU`). Apart from the other curves', so
that adding them rebuilds none of their proofs.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.Arm.Mont

open VG VG.Arm VG.Impl.Weierstrass.Arm.Mont Spec.Weierstrass.Mont

theorem mulU_arm {M : Modulus} (hM : ModOk M.k M.m) (s : State) (hs : (mulArm M).pre s) :
    ∃ t s', Exec isa (mulFnU M.k M.m) s t s' ∧ abiPreserved s s' ∧ (mulArm M).post s s' := by
  obtain ⟨t, s', he, A, K, ⟨V, C⟩, -⟩ := mulFnU_ok hM (pre_of hs.1) (by rw [← numAt_eq]; exact hs.2)
  refine ⟨t, s', he, A, ?_, ?_, keeps_of_kept hM.n9 K⟩
  · rw [numAt_eq]; exact V
  · rw [numAt_eq, numAt_eq, numAt_eq]; exact C

/-- `mulFnU` meets `mul`'s contract for any modulus the functions support, given its constant time. -/
theorem mulU_verified (M : Modulus) (hM : ModOk M.k M.m) (hk : M.k ≤ 9)
    (hct : ConstantTime isa (mulArm M).pre (mulArm M).pub (mulFnU M.k M.m)) :
    Verified Arm.target (mulFnU M.k M.m) (M.mulContract Arm.abi) :=
  Verified.of_correct (mulU_arm hM) hct
    { pre := by sig_implies_pre [Modulus.mulContract, sig, arg, mulArm, armPre, armPub, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      post := by sig_implies_post [Modulus.mulContract, sig, arg, mulArm, armPre, armPub, Arm.abi,
        Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      pub := by sig_implies_pub [Modulus.mulContract, sig, arg, mulArm, armPre, armPub, Arm.abi,
        Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      sat := ⟨sat, mul_sat M hk (VG.Proof.Mont.Arm.m_pos_of_inv hM.inv)⟩ }

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
