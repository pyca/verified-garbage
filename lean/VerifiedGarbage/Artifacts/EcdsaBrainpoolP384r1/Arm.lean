module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP384r1.Verified
public import VerifiedGarbage.Impl.Ecdsa.Verify.BrainpoolP384r1.Arm
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.BrainpoolP384r1.Verified
import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Impl.Ecdsa.Arm.VerifyHash
public import VerifiedGarbage.Spec.Ecdsa.Verify.BrainpoolP384r1
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP384r1.Lit
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.Arm
public import VerifiedGarbage.Proof.BrainpoolP384r1.Point
public import VerifiedGarbage.Proof.EcKey.PublicKey
public import VerifiedGarbage.Proof.Ecdh.Arm.Peer
public import VerifiedGarbage.Proof.Ecdsa.Arm.Lays
public import VerifiedGarbage.Proof.Ecdsa.Arm.Middle
public import VerifiedGarbage.Proof.Ecdsa.Arm.Scalar
public import VerifiedGarbage.Proof.Ecdsa.Arm.Setup
public import VerifiedGarbage.Proof.Ecdsa.Arm.SlotOps
public import VerifiedGarbage.Proof.Ecdsa.Sign
public import VerifiedGarbage.Proof.Ecdsa.Verify
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.Final
public import VerifiedGarbage.Proof.Framework.Arm.Lit
public import VerifiedGarbage.Proof.Framework.Arm.RelCT
public import VerifiedGarbage.Proof.Framework.BitByte
public import VerifiedGarbage.Proof.Rc2.Memory32
public import VerifiedGarbage.Proof.Rc2.PairMem
public import VerifiedGarbage.Proof.Rc2.Select
public import VerifiedGarbage.Proof.Rc2.Word
public import VerifiedGarbage.Proof.Weierstrass.Arm.Bits
public import VerifiedGarbage.Proof.Weierstrass.Arm.Bytes
public import VerifiedGarbage.Proof.Weierstrass.Arm.Loop
public import VerifiedGarbage.Proof.Weierstrass.Arm.Saves
public import VerifiedGarbage.Proof.Weierstrass.Pow
public import VerifiedGarbage.Proof.X25519.Arm.Limbs
public import VerifiedGarbage.Proof.X25519.Field
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.BrainpoolP384r1.Arm.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.BrainpoolP384r1

/-! # ECDSA over brainpoolP384r1 (FIPS 186-5) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.EcdsaBrainpoolP384r1.Arm

open VG.Proof.BrainpoolP384r1.Arm (hasLaw)
open VG.Proof.Ecdsa.Rfc6979.Arm (signCodeT stackT brainpoolp384r1 brainpoolp384r1T_verified brainpoolp384r1U brainpoolp384r1UT_verified)
open VG.Proof.HmacTable.Arm (tables vars)

def artifacts : List Artifact := [
  Spec.Ecdsa.BrainpoolP384r1.verifyHashApi.artifact Arm.target {
    code := Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.BrainpoolP384r1.inst.curve.len false
      Impl.Ecdsa.Verify.Arm.verifyBrainpoolP384r1
    stack := 96
    verified := Proof.Ecdsa.Verify.Arm.BrainpoolP384r1.verifyHash_verified hasLaw.law },
  Spec.Ecdsa.BrainpoolP384r1.verifyHashApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.BrainpoolP384r1.inst.curve.len false
      Impl.Ecdsa.Verify.Arm.verifyBrainpoolP384r1U
    stack := 96
    verified := Proof.Ecdsa.Verify.Arm.BrainpoolP384r1.verifyHashU_verified hasLaw.law },
  Spec.Ecdsa.Rfc6979.Curves.brainpoolp384r1SignApi.artifact Arm.target {
    tables := [("hmac", tables vars)]
    code := signCodeT (brainpoolp384r1 hasLaw.law) Spec.Ecdsa.Rfc6979.Curves.brainpoolp384r1.tries vars
    stack := stackT
    verified := brainpoolp384r1T_verified hasLaw.law },
  Spec.Ecdsa.Rfc6979.Curves.brainpoolp384r1SignApi.artifact Arm.target {
    suffix := "_umaal"
    tables := [("hmac", tables vars)]
    code := signCodeT (brainpoolp384r1U hasLaw.law) Spec.Ecdsa.Rfc6979.Curves.brainpoolp384r1.tries vars
    stack := stackT
    verified := brainpoolp384r1UT_verified hasLaw.law }]

end VG.Artifacts.EcdsaBrainpoolP384r1.Arm
