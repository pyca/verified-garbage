module

public import VerifiedGarbage.Proof.Framework.PowLit
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

@[expose] public section

namespace VG.Proof.Divstep

/-- The state of the inversion. -/
structure IState where
  d : Int
  f : Int
  g : Int
  a : Int
  b : Int

end VG.Proof.Divstep
