module

public import VerifiedGarbage.Impl.Secp256k1.X86_64.Joint

/-!
# secp256k1's point operations as functions on x86-64

`vg_secp256k1_jac_add_cached` and `vg_secp256k1_jac_add_affine`
(`Spec/Weierstrass/PointOps.lean`), with the joint verifier's products
(`publicJoint`): the code the verifier calls (`PointOps.addCachedCall`,
`addAffineCall`), which doubles equal points for `a = 0` (`dblJ0`). The
verifier's doubling stays inline, as P-384's does.
-/

@[expose] public section

namespace VG.Impl.Secp256k1.X86_64.PointOps

open VG.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass.X86_64.PointOps

/-- `vg_secp256k1_jac_add_cached`. -/
def addCachedFn : Prog isa := wrap (addCachedBody publicJoint.K publicJoint.selected dblJ0)

/-- `vg_secp256k1_jac_add_affine`. -/
def addAffineFn : Prog isa := wrap (addAffineBody publicJoint.K dblJ0)

end VG.Impl.Secp256k1.X86_64.PointOps
