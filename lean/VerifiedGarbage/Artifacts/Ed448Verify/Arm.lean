module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Ed448.Arm.Verify.Verified
public import VerifiedGarbage.Proof.Ed448.Arm.VerifyVerified
public import VerifiedGarbage.Proof.Ed448.Facts
public import VerifiedGarbage.Proof.Framework.Registration
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Impl.Ed448.Arm.Verify
public import VerifiedGarbage.Proof.Ed25519.Arm.Whole.Wrap
public import VerifiedGarbage.Proof.Ed448.Arm.ScalarLit
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Framework.TaintSum
public import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.CallCT
public import VerifiedGarbage.Proof.Ed448.Arm.BaseEncode
public import VerifiedGarbage.Proof.Ed448.Arm.BaseMain
public import VerifiedGarbage.Proof.Ed448.Arm.PublicKey.Hash
public import VerifiedGarbage.Proof.Ed448.Arm.ScalarVerified
public import VerifiedGarbage.Proof.Ed448.Arm.Verify.Hash
public import VerifiedGarbage.Proof.Ed448.Arm.VerifyDecode
public import VerifiedGarbage.Proof.Ed448.Arm.VerifyDecodeY
public import VerifiedGarbage.Proof.Ed448.Arm.VerifyFinish
public import VerifiedGarbage.Proof.Ed448.Arm.VerifyS
public import VerifiedGarbage.Proof.Ed448.Arm.VerifySign
public import VerifiedGarbage.Proof.Ed448.DecodeBytes
public import VerifiedGarbage.Proof.Ed448.Group.Decode
public import VerifiedGarbage.Proof.Ed448.Recover
public import VerifiedGarbage.Proof.Ed448.VerifyEq
public import VerifiedGarbage.Proof.Framework.Arm.NativeTaint
public import VerifiedGarbage.Proof.Framework.Arm.RegUpd
public import VerifiedGarbage.Proof.Framework.Arm.RelCT
public import VerifiedGarbage.Proof.Framework.Bswap
public import VerifiedGarbage.Proof.Framework.NativeTaintCore
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.OffsetBelow
public import VerifiedGarbage.Proof.Framework.Pratt
public import VerifiedGarbage.Proof.Sha256.Stream
public import VerifiedGarbage.Proof.Sha3.Arm.Stream.Pad
public import VerifiedGarbage.Proof.X25519.Arm.Pass
public import VerifiedGarbage.Proof.X448.Arm.Carry
public import VerifiedGarbage.Proof.X448.Arm.Copy
public import VerifiedGarbage.Proof.X448.Arm.Counters
public import VerifiedGarbage.Proof.X448.Arm.Decode
public import VerifiedGarbage.Proof.X448.Arm.DecodeAll
public import VerifiedGarbage.Proof.X448.Arm.Fill
public import VerifiedGarbage.Proof.X448.Arm.Finish
public import VerifiedGarbage.Proof.X448.Arm.Init
public import VerifiedGarbage.Proof.X448.Arm.Initial
public import VerifiedGarbage.Proof.X448.Arm.MulLoop
public import VerifiedGarbage.Proof.X448.Arm.Normalize
public import VerifiedGarbage.Proof.X448.Arm.Restore
public import VerifiedGarbage.Proof.X448.Arm.RowPass
public import VerifiedGarbage.Proof.X448.Arm.Setup
public import VerifiedGarbage.Proof.X448.Arm.Step
public import VerifiedGarbage.Proof.X448.Bytes
public import VerifiedGarbage.TCB.Arm.Print

/-! # Ed448 verification on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Ed448Verify.Arm

def artifacts : List Artifact := [
  Spec.Ed448.verifyApi.artifact Arm.target {
    code := Impl.Ed448.Arm.Verify.code
    stack := 280
    verified := Proof.Ed448.Arm.Verify.verify_verified
      (Proof.Ed448.Arm.verifyEquation_ok Proof.Ed448.recover_ok Proof.Ed448.verifyEq_ok)
      Proof.Ed448.Arm.verifyEquation_ct }]

end VG.Artifacts.Ed448Verify.Arm
