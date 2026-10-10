import VerifiedGarbage.Impl.P384.X86_64.Joint

/-!
# P-384's point operations as functions on x86-64

`vg_p384_jac_add_cached` and `vg_p384_jac_add_affine`
(`Spec/Weierstrass/PointOps.lean`), with the joint verifier's products
(`publicJoint`), and their `_adx` forms with BMI2 and ADX's
(`publicJointAdx`): the code the verifier calls (`PointOps.addCachedCall`,
`addAffineCall`). The verifier's doubling stays inline: as a call it cost
Zen 5 1–3% of a verification.
-/

namespace VG.Impl.P384.X86_64.PointOps

open VG.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass.X86_64.PointOps

/-- `vg_p384_jac_add_cached` (`adx` false) or `_adx`. -/
def addCachedFn (adx : Bool) : Prog isa :=
  wrap (addCachedBody (if adx then publicJointAdx.K else publicJoint.K) publicJoint.selected)

/-- `vg_p384_jac_add_affine` (`adx` false) or `_adx`. -/
def addAffineFn (adx : Bool) : Prog isa :=
  wrap (addAffineBody (if adx then publicJointAdx.K else publicJoint.K))

end VG.Impl.P384.X86_64.PointOps
