module

public import VerifiedGarbage.Impl.Weierstrass.X86_64
public import VerifiedGarbage.Impl.Mont.X86_64.Cms

/-!
# Short Weierstrass curves on x86-64: doubling with fused small multiples

`doubleCms M S p`: `p = 2 p` in place for `a = -3` and P-384's `p` with BMI2
and ADX, by s2n-bignum's sequence of dbl-2001-b: three products and five
squares (`Z²`, `Y²`, `(X + Z²)(X - Z²)` and its square, `X Y²`, `(Y + Z)²`,
`Y⁴`, and one more product), and the small multiples of the formula fused
into three `cms` (`C [a] - D [b] mod p`):

* `t3 = 12 X Y² - 9 ((X + Z²)(X - Z²))²`,
* `X₃ = 4 X Y² - t3`,
* `Y₃ = 3 t3 (X + Z²)(X - Z²) - 8 Y⁴`,

with `Z₃ = (Y + Z)² - Y² - Z²`. Each coordinate is read for the last time
before it is written, so the sequence needs no copy.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.X86_64

open VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64 VG.Impl.Weierstrass

/-- A step of `doubleCms`: a field operation, or `cms`. -/
inductive DStep
  | op (f : FOp)
  | cms (o C a D b : Nat)

/-- The code of a step. -/
def DStep.code (M : Mod) : DStep → List Instr
  | .op f => opCode M f
  | .cms o C a D b => Mont.X86_64.cms M o C a D b

/-- The steps of the doubling of `p` in place, through the temporaries
`t0`–`t5`. -/
def dblCmsSteps (S : RcbSlots) (p : Pt) : List DStep :=
  [.op (.mul S.t0 p.z p.z), .op (.mul S.t1 p.y p.y), .op (.add S.t2 p.x S.t0), .op (.sub S.t3 p.x S.t0),
    .op (.mul S.t4 S.t2 S.t3), .op (.add S.t2 p.y p.z), .op (.mul S.t3 S.t4 S.t4), .op (.mul S.t5 p.x S.t1),
    .op (.mul S.t2 S.t2 S.t2), .cms S.t3 12 S.t5 9 S.t3, .op (.sub S.t2 S.t2 S.t0), .op (.sub p.z S.t2 S.t1),
    .op (.mul S.t0 S.t1 S.t1), .op (.mul S.t4 S.t3 S.t4), .cms p.x 4 S.t5 1 S.t3, .cms p.y 3 S.t4 8 S.t0]

/-- `p = 2 p` in place, a block per step. -/
def doubleCms (M : Mod) (S : RcbSlots) (p : Pt) : Prog isa := blocks ((dblCmsSteps S p).map (DStep.code M))

end VG.Impl.Weierstrass.X86_64
