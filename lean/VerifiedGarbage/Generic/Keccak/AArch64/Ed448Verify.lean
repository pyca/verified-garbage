module

import VerifiedGarbage.Proof.Ed448.AArch64.Verify.Verified
public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Verified
public import VerifiedGarbage.Proof.Ed448.Facts
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ed448.AArch64.CombSum
public import VerifiedGarbage.Proof.Ed448.AArch64.Point56.Lit
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Tactic.NormNum.Prime
public import VerifiedGarbage.Impl.Ed448.AArch64.Verify
public import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Wrap
public import VerifiedGarbage.Proof.Ed448.AArch64.ScalarLit
public import VerifiedGarbage.Proof.Sha3.AArch64.Variant
public import VerifiedGarbage.Spec.Ed448.Contract
public import VerifiedGarbage.Proof.Ed448.AArch64.Verify.Verified
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.Ball
public import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejBounded
public import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejNtt
public import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.CallCT
public import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.WrapCT
public import VerifiedGarbage.Proof.Ed448.AArch64.ScalarLoop
public import VerifiedGarbage.Proof.Ed448.AArch64.ScalarVerified
public import VerifiedGarbage.Proof.Ed448.AArch64.Verify.Correct
public import VerifiedGarbage.Proof.Ed448.AArch64.Verify.Main
public import VerifiedGarbage.Proof.Ed448.AArch64.VerifyMain
public import VerifiedGarbage.Proof.Ed448.AArch64.Whole.CallsCT
public import VerifiedGarbage.Proof.Ed448.ScalarWords
public import VerifiedGarbage.Proof.Ed448.VerifyEq
public import VerifiedGarbage.Proof.Framework.AArch64.RelCT
public import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
public import VerifiedGarbage.Proof.Framework.OffsetBelow
public import VerifiedGarbage.Proof.Sha3.AArch64.Call
public import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Pad
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.Ball
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejBounded
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejNtt
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.CallCT
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.WrapCT
import VerifiedGarbage.Proof.Ed448.AArch64.ScalarLoop
import VerifiedGarbage.Proof.Ed448.AArch64.ScalarVerified
import VerifiedGarbage.Proof.Ed448.AArch64.Verify.Correct
import VerifiedGarbage.Proof.Ed448.AArch64.Verify.Main
import VerifiedGarbage.Proof.Ed448.AArch64.VerifyMain
import VerifiedGarbage.Proof.Ed448.AArch64.Whole.CallsCT
import VerifiedGarbage.Proof.Ed448.ScalarWords
import VerifiedGarbage.Proof.Ed448.VerifyEq
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Sha3.AArch64.Call
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Pad

/-! # Ed448 verification on AArch64 -/

@[expose] public section

namespace VG.Generic.Keccak.AArch64.Ed448Verify

def artifacts (v : Proof.Sha3.AArch64.Permutation) : List Artifact := [
  Spec.Ed448.verifyApi.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    consts := Impl.Ed448.AArch64.Sparse.baseConsts
    code := Impl.Ed448.AArch64.Verify.verifyWith v.callee
    stack := 352
    verified := Proof.Ed448.AArch64.Verify.verify_verified v
      (Proof.Ed448.AArch64.Sparse.verified_eqOk Proof.Ed448.recover_ok) }]

end VG.Generic.Keccak.AArch64.Ed448Verify
