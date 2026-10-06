import VerifiedGarbage.Impl.Weierstrass.Slots

namespace VG.Impl.Weierstrass

/-- Jacobian doubling when squaring uses the same implementation as multiplication.
Computing `Z' = 2YZ` directly saves two field subtractions. -/
def dblJMul (S : RcbSlots) (p o : Pt) : List FOp :=
  [.mul S.t0 p.z p.z, .mul S.t1 p.y p.y, .mul S.t2 p.x S.t1, .sub S.t3 p.x S.t0,
    .add o.x p.x S.t0, .mul S.t3 S.t3 o.x, .add o.x S.t3 S.t3, .add S.t3 o.x S.t3,
    .add S.t2 S.t2 S.t2, .add S.t2 S.t2 S.t2, .mul o.z p.y p.z, .add o.z o.z o.z, .mul o.x S.t3 S.t3, .sub o.x o.x S.t2,
    .sub o.x o.x S.t2, .sub o.y S.t2 o.x, .mul o.y S.t3 o.y, .mul S.t1 S.t1 S.t1,
    .add S.t1 S.t1 S.t1, .add S.t1 S.t1 S.t1, .add S.t1 S.t1 S.t1, .sub o.y o.y S.t1]

end VG.Impl.Weierstrass
