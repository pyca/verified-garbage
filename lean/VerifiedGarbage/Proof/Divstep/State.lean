import VerifiedGarbage.Proof.Framework.PowLit

namespace VG.Proof.Divstep

/-- The state of the inversion. -/
structure IState where
  d : Int
  f : Int
  g : Int
  a : Int
  b : Int

end VG.Proof.Divstep
