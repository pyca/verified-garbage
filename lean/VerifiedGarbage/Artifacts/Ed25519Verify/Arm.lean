module

public import VerifiedGarbage.Proof.Ed25519.Arm.VerifyVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Impl.Ed25519.Arm.ScalarBase
public import VerifiedGarbage.Proof.Ed25519.Arm.FnCall
public import VerifiedGarbage.Proof.Ed25519.Arm.MulFnFinal
public import VerifiedGarbage.Proof.Ed25519.Arm.PackField
public import VerifiedGarbage.Proof.Ed25519.Arm.PointAffine
public import VerifiedGarbage.Proof.Ed25519.Arm.PointEncode
public import VerifiedGarbage.Proof.Ed25519.Arm.PointFromScalar
public import VerifiedGarbage.Proof.Ed25519.Arm.PointMulBody
public import VerifiedGarbage.Proof.Ed25519.Arm.Points
public import VerifiedGarbage.Proof.Ed25519.Arm.RecoverCTBlocks
public import VerifiedGarbage.Proof.Ed25519.Arm.RecoverPoint
public import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTBody
public import VerifiedGarbage.Proof.Ed25519.Bytes
public import VerifiedGarbage.Proof.Framework.Arm.Call
public import VerifiedGarbage.Proof.Framework.Arm.Lit
public import VerifiedGarbage.Proof.Framework.Arm.RegUpd
public import VerifiedGarbage.Proof.X25519.Arm.AddSub
public import VerifiedGarbage.Proof.X25519.Arm.Cswap
import VerifiedGarbage.Impl.Ed25519.Arm.ScalarBase
import VerifiedGarbage.Proof.Ed25519.Arm.FnCall
import VerifiedGarbage.Proof.Ed25519.Arm.MulFnFinal
import VerifiedGarbage.Proof.Ed25519.Arm.PackField
import VerifiedGarbage.Proof.Ed25519.Arm.PointAffine
import VerifiedGarbage.Proof.Ed25519.Arm.PointEncode
import VerifiedGarbage.Proof.Ed25519.Arm.PointFromScalar
import VerifiedGarbage.Proof.Ed25519.Arm.PointMulBody
import VerifiedGarbage.Proof.Ed25519.Arm.Points
import VerifiedGarbage.Proof.Ed25519.Arm.RecoverCTBlocks
import VerifiedGarbage.Proof.Ed25519.Arm.RecoverPoint
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTBody
import VerifiedGarbage.Proof.Ed25519.Bytes
import VerifiedGarbage.Proof.Framework.Arm.Call
import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.X25519.Arm.AddSub
import VerifiedGarbage.Proof.X25519.Arm.Cswap

/-! Baseline ARMv7 Ed25519 primitive with register saves in the reviewed scratch buffer. -/

@[expose] public section

namespace VG.Artifacts.Ed25519Verify.Arm

def artifacts : List Artifact := [
  Spec.Ed25519.verifyEquationApi.artifact Arm.target {
    code := Impl.Ed25519.Arm.verifyEquation
    verified := Proof.Ed25519.Arm.verify_verified
    stack := 0 }]

end VG.Artifacts.Ed25519Verify.Arm
