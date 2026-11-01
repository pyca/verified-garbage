module

public import VerifiedGarbage.Impl.Secp256k1.X86_64.Joint

/-!
# secp256k1's point operations as functions on x86-64

`vg_secp256k1_jac_double`, `vg_secp256k1_jac_add_cached` and
`vg_secp256k1_jac_add_affine` (`Proof/Weierstrass/PointOpsContract.lean`), with the
joint verifier's products (`publicJoint`): the code the verifier calls
(`PointOps.doubleCall`, `addCachedCall`, `addAffineCall`), which doubles for
`a = 0` (`dblJ0`). Every doubling and addition of the verifier is a call of
one of them, so that each is in the code once.
-/

@[expose] public section

namespace VG.Impl.Secp256k1.X86_64.PointOps

open VG.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass.X86_64.PointOps

/-- `vg_secp256k1_jac_double`. -/
def doubleFn : Prog isa := wrap (doubleBody publicJoint.K dblJ0)

/-- `vg_secp256k1_jac_add_cached`. -/
def addCachedFn : Prog isa := wrap (addCachedBody publicJoint.K publicJoint.selected dblJ0)

/-- `vg_secp256k1_jac_add_affine`. -/
def addAffineFn : Prog isa := wrap (addAffineBody publicJoint.K dblJ0)

end VG.Impl.Secp256k1.X86_64.PointOps
