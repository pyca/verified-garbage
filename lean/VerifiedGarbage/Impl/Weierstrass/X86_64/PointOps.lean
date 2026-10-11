import VerifiedGarbage.Impl.Weierstrass.X86_64.CachedJac
import VerifiedGarbage.Impl.Weierstrass.X86_64.JacMixedForward
import VerifiedGarbage.Spec.Weierstrass.PointOps

/-!
# Short Weierstrass curves on x86-64: point operations as functions

`vg_<curve>_jac_double`, `vg_<curve>_jac_add_cached` and
`vg_<curve>_jac_add_affine` (`Spec/Weierstrass/PointOps.lean`), and their
`_adx` forms for products with BMI2 and ADX: `ws` in `rdi`, where the
curve's code keeps it. Each keeps the callee-saved registers the field
arithmetic writes (`rbp`, `r12`–`r15`) in `xmm0`–`xmm4`, which are
caller-saved, runs the code the joint verifier inlined, into `D` and copied
back to `R` (`R = P`, `E = Q`, `D = O` of the specification), and restores
them. It uses no stack and never writes `rdi`, and every address is `rdi`
plus a constant.
-/

namespace VG.Impl.Weierstrass.X86_64.PointOps

open VG.X86_64 VG.Impl.Weierstrass

/-- The callee-saved registers the field arithmetic writes, and the `xmm`
register each is kept in. -/
def kept : List (Reg × XReg) :=
  [(.rbp, .xmm0), (.r12, .xmm1), (.r13, .xmm2), (.r14, .xmm3), (.r15, .xmm4)]

def saves : List Instr := kept.map fun (r, x) => .xop (.movq x r)

def restores : List Instr := kept.map fun (r, x) => .movqR r x

/-- A function running `body`. -/
def wrap (body : Prog isa) : Prog isa := .seq (.block saves) (.seq body (.block restores))

/-- `R = 2R`, into `D` and copied back (`Joint.jacDouble`). -/
def doubleBody (K : WinCfg) : Prog isa :=
  .seq (fprogB K.M (dblJMul K.S K.R K.D)) (.block (copyPt K.M.n K.R K.D))

/-- `R = R + E` by the cached Jacobian addition, `E`'s `Z²` and `Z³` at `sel`,
into `D` and copied back. -/
def addCachedBody (K : WinCfg) (sel : Nat) : Prog isa :=
  .seq (CachedJac.add K K.R K.E K.D sel) (.block (copyPt K.M.n K.R K.D))

/-- `R = R + E` by the mixed Jacobian addition, into `D` and copied back. -/
def addAffineBody (K : WinCfg) : Prog isa :=
  .seq (Jacobian.jacMixedForward K K.R K.E K.D) (.block (copyPt K.M.n K.R K.D))

/-- The suffix of the functions with the products `K.M`. -/
def suffix (K : WinCfg) : String := if K.M.adx then "_adx" else ""

/-- A call of `vg_<curve>_jac_double`. -/
def doubleCall (C : Spec.Weierstrass.PointOps.Curve) (K : WinCfg) : Prog isa :=
  .call (C.doubleApi.name ++ suffix K) (wrap (doubleBody K))

/-- A call of `vg_<curve>_jac_add_cached`. -/
def addCachedCall (C : Spec.Weierstrass.PointOps.Curve) (K : WinCfg) (sel : Nat) : Prog isa :=
  .call (C.addCachedApi.name ++ suffix K) (wrap (addCachedBody K sel))

/-- A call of `vg_<curve>_jac_add_affine`. -/
def addAffineCall (C : Spec.Weierstrass.PointOps.Curve) (K : WinCfg) : Prog isa :=
  .call (C.addAffineApi.name ++ suffix K) (wrap (addAffineBody K))

end VG.Impl.Weierstrass.X86_64.PointOps
