module

public import VerifiedGarbage.Impl.Weierstrass.AArch64

/-!
# P-521's doubling and mixed addition in a straight line, on AArch64

Field programs with every operation inline (`program`): products and squares
by `Impl/Mont/AArch64/P521.lean` without the calls that other programs make,
and the doublings that follow each other as one multiple by a power of two
(`Step.shl`), which is a rotation.

* `double`: the doubling dbl-2001-b of the curves with `a = -3` (3 products
  and 5 squares): `δ = Z²`, `γ = Y²`, `β = Xγ`, `α = 3(X - δ)(X + δ)`,
  `X' = α² - 8β`, `Z' = (Y + Z)² - γ - δ`, `Y' = α(4β - X') - 8γ²`.
* `madd`: the mixed addition madd-2004-hmv (`maddJ`).
-/

@[expose] public section

namespace VG.Impl.Weierstrass.AArch64.P521

open VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64

/-- A field operation, or a slot's multiple by `2^k`. -/
inductive Step
  | op (f : FOp)
  | shl (k o a : Nat)

/-- The field operations a step stands for. -/
def Step.ops : Step → List FOp
  | .op f => [f]
  | .shl k o a => .add o a a :: List.replicate (k - 1) (.add o o o)

/-- A step's code. -/
def Step.code (M : Mod) : Step → List Instr
  | .op (.mul o a b) =>
    if a == b then Impl.Mont.AArch64.P521.sqrR .x0 .x0 o a else Impl.Mont.AArch64.P521.mulR .x0 .x0 .x0 o a b
  | .op f => opCode M f
  | .shl k o a => Impl.Mont.AArch64.P521.shl k o a

/-- The steps in order. -/
def program (M : Mod) (l : List Step) : Prog isa := progs (l.map fun st => .block (st.code M))

/-- The doubling of `p` into `o`. -/
def doubleSteps (S : RcbSlots) (p o : Pt) : List Step :=
  [.op (.mul S.t0 p.z p.z), .op (.mul S.t1 p.y p.y), .op (.add o.z p.y p.z), .op (.sub S.t3 p.x S.t0),
   .op (.add o.x p.x S.t0), .op (.mul S.t2 p.x S.t1), .op (.mul o.z o.z o.z), .op (.mul S.t3 S.t3 o.x),
   .op (.sub o.z o.z S.t1), .op (.sub o.z o.z S.t0), .shl 1 S.t5 S.t3, .op (.add S.t3 S.t5 S.t3),
   .op (.mul S.t1 S.t1 S.t1), .shl 3 S.t4 S.t2, .op (.mul o.x S.t3 S.t3), .shl 2 S.t2 S.t2, .op (.sub o.x o.x S.t4),
   .shl 3 S.t1 S.t1, .op (.sub o.y S.t2 o.x), .op (.mul o.y S.t3 o.y), .op (.sub o.y o.y S.t1)]

/-- The sum of `p` and the affine `q` into `o`. -/
def maddSteps (S : RcbSlots) (p q o : Pt) : List Step :=
  (maddJ S p q o).map fun
    | .add o a b => if a == b then .shl 1 o a else .op (.add o a b)
    | f => .op f

/-- `o = 2 p`. -/
def double (M : Mod) (S : RcbSlots) (p o : Pt) : Prog isa := program M (doubleSteps S p o)

/-- `o = p + q`, for an affine `q`. -/
def madd (M : Mod) (S : RcbSlots) (p q o : Pt) : Prog isa := program M (maddSteps S p q o)

end VG.Impl.Weierstrass.AArch64.P521
