module

public import VerifiedGarbage.Impl.Weierstrass.Arm.Point

/-!
# The ladder by calls of the point functions, on 32-bit ARM

`ladderP L S` is `ladder L S` (`Impl/Weierstrass/Arm.lean`) with the
doubling and the addition of an iteration as calls of
`vg_<curve>_point_double` and `vg_<curve>_point_add`
(`Impl/Weierstrass/Arm/Point.lean`), for a curve whose points fit their fixed
slots (coordinates of at most 6 words; P-521's do not, and its ladder
inlines the complete addition):

1. `G`, `a` and `3b` are copied to the slots `Q`, `a` and `3b` of the point
   functions, once;
2. an iteration copies `R` to `P`, doubles it (`O = P + P`), copies the
   double to `P`, adds `G` (`O = P + Q`), and selects `R = O` if the bit is
   set, else `P`.

A call keeps `lr` in `r10`, as the calls of the Montgomery functions do;
the point functions write neither `r10` nor `r11` and leave `r12`. Every
address is still `r12` plus a constant or a counter.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.Arm.Point

open VG.Arm VG.Impl.Mont.Arm VG.Impl.Weierstrass VG.Impl.Weierstrass.Arm
open Impl.Weierstrass.Point (elemBytes aAt b3At oAt pAt qAt)

/-- The point of the fixed slots at `o`, for coordinates of `k` words. -/
def ptAt (k o : Nat) : Pt := ⟨o, o + elemBytes k, o + 2 * elemBytes k⟩

/-- `o = a`, points of `n`-word coordinates, through `r4`. -/
def copyPt (n : Nat) (o a : Pt) : List Instr :=
  copy (2 * n) o.x a.x ++ copy (2 * n) o.y a.y ++ copy (2 * n) o.z a.z

/-- The point function a call doubles (`dbl`) or adds with: for `a0`, the
one for `a = 0` (`vg_<curve>_point_a0_double`, `vg_<curve>_point_a0_add_affine`),
else `vg_<curve>_point_double` or `vg_<curve>_point_add`. -/
def ptName (S : Impl.Weierstrass.Mont.Modulus) (a0 dbl : Bool) (u : Bool := false) : String :=
  s!"vg_{S.curve}_point_{if a0 then "a0_" else ""}{if dbl then "double" else "add"}{if a0 && !dbl then "_affine" else ""}{if u then "_umaal" else ""}"

/-- Its field operations. -/
def ptOps (a0 dbl : Bool) : List FOp := if a0 then ops0 dbl else rcb sId pId qId oId

/-- A call of the point function `ptName S a0 dbl` on the working space at
`r12`, keeping `lr` in `r10`. -/
def ptCall (S : Impl.Weierstrass.Mont.Modulus) (dbl : Bool) (a0 : Bool := false) (u : Bool := false) :
    Prog isa :=
  .seq (.block [.mov .r10 (.reg .lr), .mov .r0 (.reg wb)]) <|
    .seq (.call (ptName S a0 dbl u) (fnOps S dbl (ptOps a0 dbl) u))
      (.block [.mov .lr (.reg .r10)])

/-- `G`, `a` and `3b` to the point functions' slots. -/
def ladderSetup (L : LadderCfg) : List Instr :=
  copyPt L.M.n (ptAt L.M.n (qAt L.M.n)) L.G ++ copy (2 * L.M.n) (aAt L.M.n) L.S.a ++
    copy (2 * L.M.n) (b3At L.M.n) L.S.b3

/-- One iteration, for the bit `t = r11 - 1`: `P = R`, `O = P + P`, `P = O`,
`O = P + Q`, then `R = O` if bit `t` is set, else `P`. -/
def ladderPBody (L : LadderCfg) (S : Impl.Weierstrass.Mont.Modulus) (a0 : Bool := false) (u : Bool := false) :
    Prog isa :=
  .seq (.block [decCounter]) <| .seq (.block (copyPt L.M.n (ptAt L.M.n (pAt L.M.n)) L.R)) <|
    .seq (ptCall S true a0 u) <|
    .seq (.block (copyPt L.M.n (ptAt L.M.n (pAt L.M.n)) (ptAt L.M.n (oAt L.M.n)))) <|
    .seq (ptCall S false a0 u) <|
    .block (bitMask L.bits ++ selPt L.M.n L.R (ptAt L.M.n (pAt L.M.n)) (ptAt L.M.n (oAt L.M.n)) ++
      [testCounter])

/-- The ladder over the bits `nbits - 1` down to 0, from `R` as set up by the
caller, by calls of the point functions if the coordinates fit their slots
(for `a0`, those for `a = 0`; `G` must be affine), else `ladder`. -/
def ladderP (L : LadderCfg) (S : Impl.Weierstrass.Mont.Modulus) (a0 : Bool := false) (u : Bool := false) :
    Prog isa :=
  if L.M.n ≤ 6 then
    .seq (.block (ladderSetup L ++ [.mov .r11 (.imm (BitVec.ofNat 32 L.nbits))]))
      (.loop (ladderPBody L S a0 u) .ne)
  else ladder L S u

end VG.Impl.Weierstrass.Arm.Point
