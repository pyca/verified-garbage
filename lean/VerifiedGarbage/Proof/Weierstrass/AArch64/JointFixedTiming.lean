module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFixedDigit
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JointMixedTiming
public import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Weierstrass.AArch64

structure JointFixedChecks (c : Joint.Cfg) : Prop where
  lookup : ConstantTime isa (fun _ => True) (AArch64.Taint.AgreeS [c.tsym] (Taint.ofRegs [.x0,.x2]))
    (.block (Naf.digitIndex++Joint.fixedLoad c))
  sign : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0,.x19]))
    (.block (Naf.signRead c.G))
  neg : FieldCT (.block (VG.Impl.Mont.AArch64.sub c.K.M c.K.E.y c.K.zero c.K.E.y))
  read : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0,.x19]))
    (.block (Naf.digitRead c.G))
  mixed : JointMixedChecks c.K c.K.R c.K.E c.K.D
  copy : FieldCT (.block (copyPt 4 c.K.R c.K.D))

end VG.Proof.Weierstrass.AArch64
