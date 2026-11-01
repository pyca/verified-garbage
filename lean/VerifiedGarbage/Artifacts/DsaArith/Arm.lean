module

import VerifiedGarbage.Proof.Dsa.Arm.ArithVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.Dsa.Arm.Arith
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Weierstrass.PointContract
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Impl.Dsa.Arm.Core
public import VerifiedGarbage.Proof.Dsa.Arm.ArithVerified
public import VerifiedGarbage.Impl.Dsa.Arm.Entry
public import VerifiedGarbage.Proof.Dsa.Arithmetic
public import VerifiedGarbage.Proof.Dsa.Arm.Checks
public import VerifiedGarbage.Proof.Dsa.Arm.Doubling
public import VerifiedGarbage.Proof.Dsa.Arm.Leaves
public import VerifiedGarbage.Proof.Dsa.Digest
public import VerifiedGarbage.Proof.Dsa.Encoding
public import VerifiedGarbage.Proof.Dsa.Frame
public import VerifiedGarbage.Proof.Dsa.StreamBytes
public import VerifiedGarbage.Proof.Framework.Arm.RelCT
public import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.ContextInit
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.Csub
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.Digit
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.DigitRow
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.ExponentParts
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.Inverse
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.MulRow
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.Ops
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.PowerTwo
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.Select
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.Zeros
public import VerifiedGarbage.Proof.Mont.Read
public import VerifiedGarbage.Proof.Weierstrass.Arm.Bytes
public import VerifiedGarbage.Spec.Dsa.SignVerify
import VerifiedGarbage.Impl.Dsa.Arm.Entry
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.Arm.Checks
import VerifiedGarbage.Proof.Dsa.Arm.Doubling
import VerifiedGarbage.Proof.Dsa.Arm.Leaves
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.Frame
import VerifiedGarbage.Proof.Dsa.StreamBytes
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Mont.Arm.Dyn.ContextInit
import VerifiedGarbage.Proof.Mont.Arm.Dyn.Csub
import VerifiedGarbage.Proof.Mont.Arm.Dyn.Digit
import VerifiedGarbage.Proof.Mont.Arm.Dyn.DigitRow
import VerifiedGarbage.Proof.Mont.Arm.Dyn.ExponentParts
import VerifiedGarbage.Proof.Mont.Arm.Dyn.Inverse
import VerifiedGarbage.Proof.Mont.Arm.Dyn.MulRow
import VerifiedGarbage.Proof.Mont.Arm.Dyn.Ops
import VerifiedGarbage.Proof.Mont.Arm.Dyn.PowerTwo
import VerifiedGarbage.Proof.Mont.Arm.Dyn.Select
import VerifiedGarbage.Proof.Mont.Arm.Dyn.Zeros
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Weierstrass.Arm.Bytes
import VerifiedGarbage.Spec.Dsa.SignVerify
public import VerifiedGarbage.Proof.Weierstrass.MulContract

/-! # DSA's reductions and products on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.DsaArith.Arm

def reduceHelper (n : Nat)
    (v : Verified Arm.target (Impl.Dsa.Arm.Arith.reduceBody n)
      (Spec.Dsa.ModArith.reduceContract (Impl.Dsa.Arm.Arith.reduceLayout n) Arm.abi)) : Artifact :=
  (Spec.Dsa.ModArith.reduceApi (Impl.Dsa.Arm.Arith.reduceLayout n)).artifact Arm.target {
    code := Impl.Dsa.Arm.Arith.reduceBody n
    verified := v }

def mulHelper (n : Nat)
    (v : Verified Arm.target (Impl.Dsa.Arm.Arith.mulBody n)
      (Spec.Dsa.ModArith.mulContract (Impl.Dsa.Arm.Arith.mulLayout n) Arm.abi)) : Artifact :=
  (Spec.Dsa.ModArith.mulApi (Impl.Dsa.Arm.Arith.mulLayout n)).artifact Arm.target {
    code := Impl.Dsa.Arm.Arith.mulBody n
    verified := v }

open Proof.Dsa.Arm.Pow in
def artifacts : List Artifact := [
  reduceHelper 3 (reduceVerified 3),
  reduceHelper 4 (reduceVerified 4),
  mulHelper 3 (mulVerified 3),
  mulHelper 4 (mulVerified 4),
  mulHelper 16 (mulVerified 16),
  mulHelper 32 (mulVerified 32),
  mulHelper 48 (mulVerified 48)]

end VG.Artifacts.DsaArith.Arm
