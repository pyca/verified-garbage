module

import VerifiedGarbage.Spec.Weierstrass.CheckPoint
meta import VerifiedGarbage.Spec.Weierstrass.CheckPoint

/-!
# The contract of `Spec/Weierstrass/CheckPoint.lean`

* For every curve, `G` passes the check, and points with a coordinate changed
  by one, with `x = p` or with `y = p` (`G`'s coordinates plus `p`) fail it;
* the function's own working space and its results are apart from what the
  caller provides (`p`, `R² mod p`, `a R mod p`, `b R mod p`, `G`, `x`, `y`),
  and its own working space from its results.
-/

namespace VG.Test.WeierstrassCheckPoint

open Spec.Weierstrass Spec.Weierstrass.CheckPoint

/-- `G` passes, and its neighbours and lifts by `p` fail. -/
def checkValid (C : CheckPoint.Curve) : Bool :=
  let gx := C.W.gx
  let gy := C.W.gy
  decide (C.Valid gx gy) && !decide (C.Valid gx (gy + 1)) && !decide (C.Valid (gx + 1) gy) &&
    !decide (C.Valid (gx + C.W.p) gy) && !decide (C.Valid gx (gy + C.W.p))

/-- The bytes of the numbers the caller provides. -/
def inputs (C : CheckPoint.Curve) : List (Nat × Nat) :=
  [C.pAt, C.r2At, C.aAt, C.bAt, C.gxAt, C.gyAt, C.xAt, C.yAt].map (·, 8 * C.k)

/-- The bytes of the results. -/
def outputs (C : CheckPoint.Curve) : List (Nat × Nat) :=
  [C.xmAt, C.ymAt, C.pxAt, C.pyAt].map (·, 8 * C.k) ++ [(C.flagAt, 8)]

/-- The bytes of the own working space. -/
def own (C : CheckPoint.Curve) : List (Nat × Nat) :=
  [2, 37, 41, 42].map (fun j => (C.slot j, 8 * C.k)) ++ [(Mont.ownAt C.k, Mont.ownBytes C.k)]

def apart (a b : Nat × Nat) : Bool := a.1 + a.2 ≤ b.1 || b.1 + b.2 ≤ a.1

/-- The own working space and the results are apart from the inputs, and from
each other; the flag's word is inside the flag's slot and everything below
byte 4096. -/
def checkLayout (C : CheckPoint.Curve) : Bool :=
  (own C ++ outputs C).all (fun r => (inputs C).all (apart r)) &&
    (own C).all (fun r => (outputs C).all (apart r)) &&
    (inputs C ++ outputs C ++ own C).all (fun r => r.1 + r.2 ≤ 4096)

#guard curves.all checkValid
#guard curves.all checkLayout

end VG.Test.WeierstrassCheckPoint
