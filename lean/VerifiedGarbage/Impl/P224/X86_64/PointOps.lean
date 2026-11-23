module

public import VerifiedGarbage.Impl.P224.X86_64.Joint

/-!
# P-224's point operations as functions on x86-64

`vg_p224_jac_double`, `vg_p224_jac_add_cached` and `vg_p224_jac_add_affine`
(`Proof/Weierstrass/PointOpsContract.lean`), with the joint verifier's
products (`publicJoint`): the code the verifier calls (`PointOps.doubleCall`,
`addCachedCall`, `addAffineCall`), which doubles for `a = -3` (`dblJMul`).
Every doubling and addition of the verifier is a call of one of them, so that
each is in the code once.
-/

@[expose] public section

namespace VG.Impl.P224.X86_64.PointOps

open VG.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass.X86_64.PointOps

/-- `vg_p224_jac_double`. -/
def doubleFn : Prog isa := wrap (doubleBody publicJoint.K dblJMul)

/-- `vg_p224_jac_add_cached`. -/
def addCachedFn : Prog isa :=
  wrap (addCachedBody publicJoint.K publicJoint.selected dblJMul (tailCall Impl.Weierstrass.PointOps.p224 publicJoint.K dblJMul))

/-- `vg_p224_jac_add_affine`. -/
def addAffineFn : Prog isa :=
  wrap (addAffineBody publicJoint.K dblJMul (tailCall Impl.Weierstrass.PointOps.p224 publicJoint.K dblJMul))

/-- `vg_p224_jac_add_tail`, which both additions call. -/
def tailFn : Prog isa := tailBody publicJoint.K dblJMul

end VG.Impl.P224.X86_64.PointOps
