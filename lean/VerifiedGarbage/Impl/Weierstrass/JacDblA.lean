module

public import VerifiedGarbage.Impl.Weierstrass.Slots

/-!
# Jacobian doubling for any `a`

`dblJa`, the doubling of the windows of every curve whose `a` is neither 0 nor
-3 (the brainpool curves), on every target that runs them.
-/

@[expose] public section

namespace VG.Impl.Weierstrass

/-- `o = 2p` in Jacobian coordinates for any `a`, at the slot `S.a`
(dbl-2007-bl, with `Z' = 2YZ` as a product): `A = X²`, `B = Y²`, `C = B²`,
`D = 2 ((X + B)² - A - C)`, `M = 3A + a (Z²)²`, `Z' = 2YZ`, `X' = M² - 2D`,
`Y' = M (D - X') - 8C`; 9 products and 1 by `a` (temporaries `t0 … t5`;
`o` apart from `p`). -/
def dblJa (S : RcbSlots) (p o : Pt) : List FOp :=
  [.mul S.t0 p.x p.x, .mul S.t1 p.y p.y, .mul S.t2 S.t1 S.t1, .add S.t3 p.x S.t1,
   .mul S.t3 S.t3 S.t3, .sub S.t3 S.t3 S.t0, .sub S.t3 S.t3 S.t2, .add S.t3 S.t3 S.t3,
   .mul S.t4 p.z p.z, .mul S.t4 S.t4 S.t4, .mul S.t4 S.a S.t4, .add S.t5 S.t0 S.t0,
   .add S.t5 S.t5 S.t0, .add S.t4 S.t4 S.t5, .mul o.z p.y p.z, .add o.z o.z o.z,
   .mul o.x S.t4 S.t4, .sub o.x o.x S.t3, .sub o.x o.x S.t3, .sub o.y S.t3 o.x,
   .mul o.y S.t4 o.y, .add S.t2 S.t2 S.t2, .add S.t2 S.t2 S.t2, .add S.t2 S.t2 S.t2,
   .sub o.y o.y S.t2]

end VG.Impl.Weierstrass
