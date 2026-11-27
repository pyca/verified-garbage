module

import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAdd
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAddTiming
public import VerifiedGarbage.Impl.Weierstrass.AArch64.JointMixed
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Arithmetic
import VerifiedGarbage.Proof.Weierstrass.AArch64.Blocks
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacMixedAdd
public import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
public import VerifiedGarbage.Impl.Weierstrass.AArch64.Joint
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256Bounds

/-! ### `Weierstrass.AArch64.JointMixedTiming`, which only this module used -/

section

/-! Public-data mixed Jacobian addition retains a common field environment. -/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass
open VG.Impl.Weierstrass.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64

structure JointMixedChecks (K : WinCfg) (p q o : Pt) : Prop where
  zero : ∀ a∈[p.z,K.S.t3,K.S.t5], FieldCT (.block (zeroMask K.M.n a))
  copyQ : FieldCT (.block (copyPt K.M.n o q))
  init : FieldCT (.block (copy K.M.n K.S.t2 p.x ++ copy K.M.n K.S.t4 p.y))
  head : FieldCT (VG.Impl.P256.VerifyArithmetic.program K.M (jacMixedHead K.S p q))
  tail : FieldCT (VG.Impl.P256.VerifyArithmetic.program K.M (jacMixedTail K.S p q o))
  double : FieldCT (VG.Impl.P256.VerifyDouble.double K.M K.S p o)
  infinity : FieldCT (.block (Jacobian.infinity K o))

end VG.Proof.Weierstrass.AArch64

end

end


@[expose] public section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Weierstrass.AArch64

/-- The registers the table lookup's address depends on: the digit's byte, and for width nine its
high byte. -/
def jointGPub (c : Joint.Cfg) : List Reg := if c.gw=9 then [.x0,.x2,.x3] else [.x0,.x2]

structure JointFixedChecks (c : Joint.Cfg) : Prop where
  lookup : ConstantTime isa (fun _ => True) (AArch64.Taint.AgreeS [c.tsym] (Taint.ofRegs (jointGPub c)))
    (.block (Joint.fixedIndex c++Joint.fixedLoad c))
  sign : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0,.x19]))
    (.block (Joint.signRead c))
  neg : FieldCT (.block (VG.Impl.Mont.AArch64.sub c.K.M c.K.E.y c.K.zero c.K.E.y))
  read : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0,.x19]))
    (.block (Joint.fixedRead c))
  mixed : JointMixedChecks c.K c.K.R c.K.E c.K.D
  copy : FieldCT (.block (copyPt 4 c.K.R c.K.D))

end VG.Proof.Weierstrass.AArch64
