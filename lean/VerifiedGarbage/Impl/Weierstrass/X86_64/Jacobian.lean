import VerifiedGarbage.Impl.Weierstrass.JacAdd
import VerifiedGarbage.Impl.Weierstrass.X86_64.Window

/-! Jacobian point operations for public verification data. -/
namespace VG.Impl.Weierstrass.X86_64.Jacobian
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64 VG.Impl.Weierstrass

def zeroTest (n a : Nat) : List Instr :=
  [.mov .rdx (.mem (sc a))] ++
    ((List.range (n-1)).map fun i => .alu .or .rdx (.mem (sc (a+8*(i+1))))) ++
    [.alu .test .rdx (.reg .rdx)]

def infinity (K : WinCfg) (o : Pt) : List Instr :=
  setConst K.M.n o.x 0 ++ setConst K.M.n o.y K.one ++ setConst K.M.n o.z 0

def jacAdd (K : WinCfg) (p q o : Pt) : Prog isa :=
  .seq (.block (zeroTest K.M.n p.z)) <|
  .ite .e (.block (copyPt K.M.n o q)) <|
  .seq (.block (zeroTest K.M.n q.z)) <|
  .ite .e (.block (copyPt K.M.n o p)) <|
  .seq (fprogB K.M (jacHead K.S p q)) <|
  .seq (.block (zeroTest K.M.n K.S.t3)) <|
  .ite .e
    (.seq (.block (zeroTest K.M.n K.S.t5)) <|
      .ite .e (fprogB K.M (dblJMul K.S p o)) (.block (infinity K o)))
    (fprogB K.M (jacTail K.S p q o))
def jacMixedAdd (K : WinCfg) (p q o : Pt) : Prog isa :=
  let head := jacMixedHead K.S p q
  let tail := jacMixedTail K.S p q o
  .seq (.block (zeroTest K.M.n p.z)) <|
  .ite .e (.block (copyPt K.M.n o q)) <|
  .seq (.block (copy K.M.n K.S.t2 p.x ++ copy K.M.n K.S.t4 p.y)) <|
  .seq (fprogB K.M head) <|
  .seq (.block (zeroTest K.M.n K.S.t3)) <|
  .ite .e
    (.seq (.block (zeroTest K.M.n K.S.t5)) <|
      .ite .e (fprogB K.M (dblJMul K.S p o)) (.block (infinity K o)))
    (fprogB K.M tail)

end VG.Impl.Weierstrass.X86_64.Jacobian
