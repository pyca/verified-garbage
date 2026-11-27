module

public import VerifiedGarbage.Impl.P384.Linear
public import VerifiedGarbage.Impl.Ecdh.AArch64.WindowJ

/-!
# P-384's doubling for the windows on AArch64

`raw p o` is the doubling `o = 2 p` in Jacobian coordinates for `a = -3`, in a
straight line of steps. With `d = Z²`, `g = Y²`, `b = X g` and `v = (X - d)(X + d)`, the
tangent's slope is `3v / 2YZ`, and

    X' = 9v² - 8b,  Y' = 3v(4b - X') - 8g²,  Z' = 2YZ,

four products, four squares and six sums, three of which are fused
(`Linear.lean`). It uses the registers `x1`–`x17` and `x21`–`x25`, which ECDH and
ECDSA save on entry.
-/

@[expose] public section

namespace VG.Impl.P384.EcdhDouble
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64

/-- The window as ECDH and ECDSA over P-384 have it. -/
def K : WinCfg := Impl.Ecdsa.AArch64.p384.winCfg Impl.Ecdh.AArch64.PX Impl.Ecdh.AArch64.PY

/-- A step of the doubling: a field operation or a fused combination. -/
inductive Step
  | op (f : FOp)
  | lin98 (o a b : Nat)
  | lin41 (o a b : Nat)
  | lin38 (o a b : Nat)

/-- A step's code. -/
def Step.code : Step → List Instr
  | .op f => Ops.op f
  | .lin98 o a b => Linear.lin98 o a b
  | .lin41 o a b => Linear.lin41 o a b
  | .lin38 o a b => Linear.lin38 o a b

/-- The steps of `o = 2 p`. -/
def steps (S : RcbSlots) (p o : Pt) : List Step :=
  [.op (.mul S.t0 p.z p.z), .op (.mul S.t1 p.y p.y), .op (.sub S.t2 p.x S.t0), .op (.add S.t3 p.x S.t0),
   .op (.mul S.t4 p.x S.t1), .op (.mul S.t2 S.t2 S.t3), .op (.mul o.z p.y p.z), .op (.mul S.t3 S.t2 S.t2),
   .op (.mul S.t1 S.t1 S.t1), .op (.add o.z o.z o.z), .lin98 o.x S.t3 S.t4, .lin41 S.t4 S.t4 o.x,
   .op (.mul S.t2 S.t2 S.t4), .lin38 o.y S.t2 S.t1]

/-- `o = 2 p`. -/
def raw (p o : Pt) : List Instr := (steps K.S p o).flatMap Step.code

/-- The registers it changes. -/
def regs : List Reg := [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17,
  .x21, .x22, .x23, .x24, .x25]

/-- The window's doublings, of the accumulator `R` into `D` and back. -/
def doubleRD : List Instr := raw K.R K.D
def doubleDR : List Instr := raw K.D K.R

/-- The shared straight-line bodies, also used by ECDSA verification. -/
def doubleRDBody : Prog isa := .block doubleRD
def doubleDRBody : Prog isa := .block doubleDR

/-- Keep the outer link register in a lane the scalar doubling does not write. -/
def callDouble (name : String) (body : Prog isa) : Prog isa :=
  .seq (.block [.vop (.ins .d2 .v31 1 .x30)])
    (.seq (.call name body) (.block [.umov .x .x30 .v31 1]))

def callRD : Prog isa := callDouble "vg_p384_window_double_rd" doubleRDBody
def callDR : Prog isa := callDouble "vg_p384_window_double_dr" doubleDRBody

end VG.Impl.P384.EcdhDouble
