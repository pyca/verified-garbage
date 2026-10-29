module
public import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.P384Joint
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAddTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256Bounds
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot
import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowBase
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
meta import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.P384Joint
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAddTiming
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256Bounds
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowBase
@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
open VG VG.AArch64 VG.Impl.Weierstrass.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Weierstrass.AArch64

theorem fixedLookup_ct : ConstantTime isa (fun _ => True)
 (Taint.AgreeS ["VG_P384_GTAB"] (Taint.ofRegs [.x0,.x2,.x3])) (.block P384Joint.fixedLoad) :=
 VG.Taint.constantTime (A:=taintS ["VG_P384_GTAB"]) (Taint.ofRegs [.x0,.x2,.x3])
 (fun _ _ _ _ h=>h) (by taint_decide)

theorem fixedRead_ct : ConstantTime isa (fun _ => True)
 (AArch64.Taint.Agree (Taint.ofRegs [.x0,.x19])) (.block (Joint.fixedRead P384Joint.cfg)) :=
 VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.x0,.x19]) (fun _ _ _ _ h=>h) (by taint_decide)

theorem fixedSign_ct : ConstantTime isa (fun _ => True)
 (AArch64.Taint.Agree (Taint.ofRegs [.x0,.x19])) (.block (Joint.signRead P384Joint.cfg)) :=
 VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.x0,.x19]) (fun _ _ _ _ h=>h) (by taint_decide)

theorem fixedNeg_ct : FieldCT (.block (Impl.Mont.AArch64.sub P384Joint.K.M P384Joint.K.E.y P384Joint.K.zero P384Joint.K.E.y)) :=
 VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.x0]) (fun _ _ _ _ h=>h) (by taint_decide)

theorem fixedCopy_ct : FieldCT (.block (copyPt 6 P384Joint.K.R P384Joint.K.D)) :=
 VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.x0]) (fun _ _ _ _ h=>h) (by taint_decide)
end VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
