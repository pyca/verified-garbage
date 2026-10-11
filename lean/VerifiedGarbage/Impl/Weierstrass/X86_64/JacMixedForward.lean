module

public import VerifiedGarbage.Impl.Weierstrass.X86_64.Jacobian
public import VerifiedGarbage.Impl.Weierstrass.X86_64.ForwardField

/-! Public mixed Jacobian addition with register forwarding between field operations. -/

@[expose] public section

namespace VG.Impl.Weierstrass.X86_64.Jacobian
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64 VG.Impl.Weierstrass

def jacMixedForward (K : WinCfg) (p q o : Pt) : Prog isa :=
  let head := jacMixedHead K.S p q
  let tail := jacMixedTail K.S p q o
  .seq (.block (zeroTest K.M.n p.z)) <|
  .ite .e (.block (copyPt K.M.n o q)) <|
  .seq (.block (copy K.M.n K.S.t2 p.x ++ copy K.M.n K.S.t4 p.y)) <|
  .seq (ForwardField.programB K.M head) <|
  .seq (.block (zeroTest K.M.n K.S.t3)) <|
  .ite .e
    (.seq (.block (zeroTest K.M.n K.S.t5)) <|
      .ite .e (ForwardField.programB K.M (dblJMul K.S p o)) (.block (infinity K o)))
    (ForwardField.programB K.M tail)


end VG.Impl.Weierstrass.X86_64.Jacobian
