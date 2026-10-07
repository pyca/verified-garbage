import VerifiedGarbage.Impl.Weierstrass.X86_64.Joint

/-! A doubler for the joint loop's accumulator, for any number of words. -/
namespace VG.Impl.Weierstrass.X86_64.Joint
open VG VG.X86_64 VG.Impl.Weierstrass

/-- `R = [2]R`: Jacobian doubling (`dblJMul`, 2004 formulas for `a = -3` with
direct products) into `D`, copied back to `R`. -/
def jacDouble (K : WinCfg) : Prog isa :=
  .seq (fprogB K.M (dblJMul K.S K.R K.D)) (.block (copyPt K.M.n K.R K.D))

end VG.Impl.Weierstrass.X86_64.Joint
