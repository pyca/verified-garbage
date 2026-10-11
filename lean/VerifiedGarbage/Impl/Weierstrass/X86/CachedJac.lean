module

public import VerifiedGarbage.Impl.Weierstrass.JacAdd

/-! Jacobian addition using the selected point's cached powers of Z. -/

@[expose] public section

namespace VG.Impl.Weierstrass.X86.CachedJac
open VG VG.Impl.Weierstrass

def head (n : Nat) (S : RcbSlots) (p q : Pt) (dst : Nat) : List FOp :=
  [.mul S.t0 p.z p.z,.mul S.t2 p.x dst,.mul S.t3 q.x S.t0,
   .mul S.t4 p.y (dst+8*n),.mul S.t5 q.y p.z,.mul S.t5 S.t5 S.t0,
   .sub S.t3 S.t3 S.t2,.sub S.t5 S.t5 S.t4]

end VG.Impl.Weierstrass.X86.CachedJac
