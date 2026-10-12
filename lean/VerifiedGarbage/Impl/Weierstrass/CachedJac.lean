module

public import VerifiedGarbage.Impl.Weierstrass.JacAdd

@[expose] public section

namespace VG.Impl.Weierstrass.CachedJac

/-- Cached powers of the selected public table point's Jacobian Z coordinate. -/
def z2 : Nat := 5400
def z3 : Nat := 5432

def tableZ2 (i : Nat) : Nat := 6000 + 64*i
def tableZ3 (i : Nat) : Nat := 6032 + 64*i

/-- Addition header using a table entry's precomputed Z² and Z³. -/
def head (S : RcbSlots) (p q : Pt) : List FOp :=
  [.mul S.t0 p.z p.z,
   .mul S.t2 p.x z2,.mul S.t3 q.x S.t0,
   .mul S.t4 p.y z3,
   .mul S.t5 q.y p.z,.mul S.t5 S.t5 S.t0,
   .sub S.t3 S.t3 S.t2,.sub S.t5 S.t5 S.t4]

end VG.Impl.Weierstrass.CachedJac
