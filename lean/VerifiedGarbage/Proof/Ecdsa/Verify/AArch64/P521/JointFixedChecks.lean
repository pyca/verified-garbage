module
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointFixedEntry
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTableTiming
public import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
meta import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.P521Joint
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.P521.Joint
open VG VG.AArch64 VG.Impl.Weierstrass.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Weierstrass.AArch64

theorem fixedLookup_ct : ConstantTime isa (fun _ => True)
 (Taint.AgreeS ["VG_P521_COMB"] (Taint.ofRegs [.x0,.x2])) (.block P521Joint.fixedLoad) :=
 VG.Taint.constantTime (A:=taintS ["VG_P521_COMB"]) (Taint.ofRegs [.x0,.x2])
 (fun _ _ _ _ h=>h) (by taint_decide)

theorem fixedRead_ct : ConstantTime isa (fun _ => True)
 (AArch64.Taint.Agree (Taint.ofRegs [.x0,.x19])) (.block (Naf.digitRead P521Joint.KG)) :=
 VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.x0,.x19]) (fun _ _ _ _ h=>h) (by taint_decide)

theorem fixedSign_ct : ConstantTime isa (fun _ => True)
 (AArch64.Taint.Agree (Taint.ofRegs [.x0,.x19])) (.block (Naf.signRead P521Joint.KG)) :=
 VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.x0,.x19]) (fun _ _ _ _ h=>h) (by taint_decide)

theorem fixedNeg_ct : FieldCT (.block (Impl.Mont.AArch64.sub P521Joint.K.M P521Joint.K.E.y P521Joint.K.zero P521Joint.K.E.y)) :=
 VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.x0]) (fun _ _ _ _ h=>h) (by taint_decide)

theorem fixedCopy_ct : FieldCT (.block (copyPt 9 P521Joint.K.R P521Joint.K.D)) :=
 VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.x0]) (fun _ _ _ _ h=>h) (by taint_decide)
end VG.Proof.Ecdsa.Verify.AArch64.P521.Joint
