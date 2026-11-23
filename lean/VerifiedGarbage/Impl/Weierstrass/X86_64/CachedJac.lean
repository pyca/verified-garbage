module

public import VerifiedGarbage.Impl.Weierstrass.X86_64.Jacobian
public import VerifiedGarbage.Impl.Weierstrass.X86_64.ForwardField

/-! Jacobian addition using the selected point's cached powers of Z. -/

@[expose] public section

namespace VG.Impl.Weierstrass.X86_64.CachedJac
open VG VG.X86_64 VG.Impl.Weierstrass

def head (n : Nat) (S : RcbSlots) (p q : Pt) (dst : Nat) : List FOp :=
  [.mul S.t0 p.z p.z,.mul S.t2 p.x dst,.mul S.t3 q.x S.t0,
   .mul S.t4 p.y (dst+8*n),.mul S.t5 q.y p.z,.mul S.t5 S.t5 S.t0,
   .sub S.t3 S.t3 S.t2,.sub S.t5 S.t5 S.t4]

/-- `head`, with `o.z = Z1 Z2` first, which the end of the addition (`addEnd`)
multiplies by `H`. -/
def headZ (n : Nat) (S : RcbSlots) (p q o : Pt) (dst : Nat) : List FOp :=
  .mul o.z p.z q.z :: head n S p q dst

/-- The end of the Jacobian additions, from `U1`, `S1`, `H`, `r` in `t2`,
`t4`, `t3`, `t5` and `Z` in `o.z` (`jacEndTail`): the double of `p` by `dbl`
for `H = r = 0`, the point at infinity for `H = 0` but not `r`, else the
sum. The code of `vg_<curve>_jac_add_tail`, which both additions call. -/
def addEnd (K : WinCfg) (p q o : Pt) (dbl : RcbSlots → Pt → Pt → List FOp := dblJMul) : Prog isa :=
  .seq (.block (Jacobian.zeroTest K.M.n K.S.t3)) <|
  .ite .e
    (.seq (.block (Jacobian.zeroTest K.M.n K.S.t5)) <|
      .ite .e (ForwardField.programB K.M (dbl K.S p o)) (.block (Jacobian.infinity K o)))
    (ForwardField.programB K.M (jacEndTail K.S p q o))

/-- `o = p + q`, `q`'s `Z²` and `Z³` at `dst`, the double of `p` by `dbl` if
they are equal (`dblJMul` for `a = -3`): the header (`headZ`), then `fin`,
the end (`addEnd`, or a call of it). -/
def add (K : WinCfg) (p q o : Pt) (dst : Nat) (dbl : RcbSlots → Pt → Pt → List FOp := dblJMul)
    (fin : Prog isa := addEnd K p q o dbl) : Prog isa :=
  .seq (.block (Jacobian.zeroTest K.M.n p.z)) <|
  .ite .e (.block (copyPt K.M.n o q)) <|
  .seq (.block (Jacobian.zeroTest K.M.n q.z)) <|
  .ite .e (.block (copyPt K.M.n o p)) <|
  .seq (ForwardField.programB K.M (headZ K.M.n K.S p q o dst)) fin

end VG.Impl.Weierstrass.X86_64.CachedJac
