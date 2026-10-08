import VerifiedGarbage.Impl.Weierstrass.JacAdd
import VerifiedGarbage.Impl.Weierstrass.X86.Window

/-! Jacobian point operations for public verification data. -/
namespace VG.Impl.Weierstrass.X86.Jacobian
open VG VG.X86 VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Weierstrass

def zeroTest (n a : Nat) : List Instr :=
  [.mov .edx (.mem (sc a))] ++
    ((List.range (2*n-1)).map fun i => .alu .or .edx (.mem (sc (a+4*(i+1))))) ++
    [.alu .test .edx (.reg .edx)]

def infinity (K : WinCfg) (o : Pt) : List Instr :=
  setConst K.M.n o.x 0 ++ setConst K.M.n o.y K.one ++ setConst K.M.n o.z 0

def jacAdd (K : WinCfg) (F : Spec.Weierstrass.Mont.Modulus) (p q o : Pt) : Prog isa :=
  .seq (.block (zeroTest K.M.n p.z)) <|
  .ite .e (.block (copyPt K.M.n o q)) <|
  .seq (.block (zeroTest K.M.n q.z)) <|
  .ite .e (.block (copyPt K.M.n o p)) <|
  .seq (fprog F (jacHead K.S p q)) <|
  .seq (.block (zeroTest K.M.n K.S.t3)) <|
  .ite .e
    (.seq (.block (zeroTest K.M.n K.S.t5)) <|
      .ite .e (fprog F (dblJMul K.S p o)) (.block (infinity K o)))
    (fprog F (jacTail K.S p q o))

end VG.Impl.Weierstrass.X86.Jacobian
