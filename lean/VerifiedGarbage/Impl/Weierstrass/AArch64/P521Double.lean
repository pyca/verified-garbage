module

public import VerifiedGarbage.Impl.Weierstrass.AArch64

/-! # P-521 Jacobian doubling with fused small linear combinations -/

@[expose] public section

namespace VG.Impl.Weierstrass.AArch64.P521Double

open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64

inductive Step
  | op (f : FOp)
  | cms (o C a D b : Nat)

def Step.code (M : Mod) : Step → Prog isa
  | .op f => opProg M f
  | .cms o C a D b => .block (P521Linear.cms o C a D b)

/-- The `a = -3` doubling used on x86-64, with a separate output point. -/
def steps (S : RcbSlots) (p o : Pt) : List Step :=
  [.op (.mul S.t0 p.z p.z), .op (.mul S.t1 p.y p.y), .op (.add S.t2 p.x S.t0), .op (.sub S.t3 p.x S.t0),
   .op (.mul S.t4 S.t2 S.t3), .op (.add S.t2 p.y p.z), .op (.mul S.t3 S.t4 S.t4), .op (.mul S.t5 p.x S.t1),
   .op (.mul S.t2 S.t2 S.t2), .cms S.t3 12 S.t5 9 S.t3, .op (.sub S.t2 S.t2 S.t0), .op (.sub o.z S.t2 S.t1),
   .op (.mul S.t0 S.t1 S.t1), .op (.mul S.t4 S.t3 S.t4), .cms o.x 4 S.t5 1 S.t3, .cms o.y 3 S.t4 8 S.t0]

def program (M : Mod) : List Step → Prog isa
  | [] => .block []
  | st::ss => .seq (st.code M) (program M ss)

def double (M : Mod) (S : RcbSlots) (p o : Pt) : Prog isa := program M (steps S p o)

end VG.Impl.Weierstrass.AArch64.P521Double
