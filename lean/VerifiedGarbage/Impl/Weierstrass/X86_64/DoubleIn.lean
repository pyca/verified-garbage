import VerifiedGarbage.Impl.Weierstrass.JacMul
import VerifiedGarbage.Impl.Weierstrass.X86_64.ForwardField

/-!
# Short Weierstrass curves on x86-64: doubling a Jacobian point in place

`doubleIn M S p`: `p = 2 p` for `a = -3`, by `dblJMul` (dbl-2001-b with the
direct product `Z₃ = 2 Y Z`) with `p` as both its input and its output. Each
coordinate is read for the last time before it is written (`X` by `X + Z²`,
the first write of `X₃`; `Y` and `Z` by `Y Z`, before `Z₃` and `Y₃`), so the
in-place sequence computes the doubling, with no copy.
-/

namespace VG.Impl.Weierstrass.X86_64

open VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass

/-- `p = 2 p` in place, through the temporaries `t0`–`t3`. -/
def doubleIn (M : Mod) (S : RcbSlots) (p : Pt) : Prog isa := ForwardField.programB M (dblJMul S p p)

end VG.Impl.Weierstrass.X86_64
