import VerifiedGarbage.Impl.Weierstrass.X86_64.Jacobian
import VerifiedGarbage.Impl.Weierstrass.X86_64.ForwardField

/-! Jacobian addition using the selected point's cached powers of Z. -/
namespace VG.Impl.Weierstrass.X86_64.CachedJac
open VG VG.X86_64 VG.Impl.Weierstrass

def head (S : RcbSlots) (p q : Pt) (dst : Nat) : List FOp :=
  [.mul S.t0 p.z p.z,.mul S.t2 p.x dst,.mul S.t3 q.x S.t0,
   .mul S.t4 p.y (dst+32),.mul S.t5 q.y p.z,.mul S.t5 S.t5 S.t0,
   .sub S.t3 S.t3 S.t2,.sub S.t5 S.t5 S.t4]

def add (K : WinCfg) (p q o : Pt) (dst : Nat) : Prog isa :=
  .seq (.block (Jacobian.zeroTest K.M.n p.z)) <|
  .ite .e (.block (copyPt K.M.n o q)) <|
  .seq (.block (Jacobian.zeroTest K.M.n q.z)) <|
  .ite .e (.block (copyPt K.M.n o p)) <|
  .seq (ForwardField.programB K.M (head K.S p q dst)) <|
  .seq (.block (Jacobian.zeroTest K.M.n K.S.t3)) <|
  .ite .e
    (.seq (.block (Jacobian.zeroTest K.M.n K.S.t5)) <|
      .ite .e (ForwardField.programB K.M (dblJMul K.S p o)) (.block (Jacobian.infinity K o)))
    (ForwardField.programB K.M (jacTail K.S p q o))

end VG.Impl.Weierstrass.X86_64.CachedJac
