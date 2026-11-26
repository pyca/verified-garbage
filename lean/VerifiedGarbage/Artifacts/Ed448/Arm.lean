module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.Proof.Ed448.Arm.Scrub
import VerifiedGarbage.Proof.Ed448.Arm.PublicKey.Verified
import VerifiedGarbage.Proof.Ed448.Facts
import VerifiedGarbage.Proof.Ed448.CombFacts
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Variants.Curve448Field.Arm
import VerifiedGarbage.Proof.Ed448.Arm.SignCached.Verified
import VerifiedGarbage.Proof.Ed448.Arm.Verify.Verified
import VerifiedGarbage.Proof.Ed448.Arm.VerifyVerified
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.Set
import VerifiedGarbage.Impl.Ed448.Arm.Verify
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.Wrap
import VerifiedGarbage.Proof.Ed448.Arm.ScalarLit
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.TaintSum
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.CallCT
import VerifiedGarbage.Proof.Ed448.Arm.BaseEncode
import VerifiedGarbage.Proof.Ed448.Arm.BaseMain
import VerifiedGarbage.Proof.Ed448.Arm.PublicKey.Hash
import VerifiedGarbage.Proof.Ed448.Arm.ScalarVerified
import VerifiedGarbage.Proof.Ed448.Arm.Verify.Hash
import VerifiedGarbage.Proof.Ed448.Arm.VerifyDecode
import VerifiedGarbage.Proof.Ed448.Arm.VerifyDecodeY
import VerifiedGarbage.Proof.Ed448.Arm.VerifyFinish
import VerifiedGarbage.Proof.Ed448.Arm.VerifyS
import VerifiedGarbage.Proof.Ed448.Arm.VerifySign
import VerifiedGarbage.Proof.Ed448.DecodeBytes
import VerifiedGarbage.Proof.Ed448.Group.Decode
import VerifiedGarbage.Proof.Ed448.Recover
import VerifiedGarbage.Proof.Ed448.VerifyEq
import VerifiedGarbage.Proof.Framework.Arm.NativeTaint
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.Pratt
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Sha3.Arm.Stream.Pad
import VerifiedGarbage.Proof.X25519.Arm.Pass
import VerifiedGarbage.Proof.X448.Arm.Carry
import VerifiedGarbage.Proof.X448.Arm.Copy
import VerifiedGarbage.Proof.X448.Arm.Counters
import VerifiedGarbage.Proof.X448.Arm.Decode
import VerifiedGarbage.Proof.X448.Arm.DecodeAll
import VerifiedGarbage.Proof.X448.Arm.Fill
import VerifiedGarbage.Proof.X448.Arm.Finish
import VerifiedGarbage.Proof.X448.Arm.Init
import VerifiedGarbage.Proof.X448.Arm.Initial
import VerifiedGarbage.Proof.X448.Arm.MulLoop
import VerifiedGarbage.Proof.X448.Arm.Normalize
import VerifiedGarbage.Proof.X448.Arm.Restore
import VerifiedGarbage.Proof.X448.Arm.RowPass
import VerifiedGarbage.Proof.X448.Arm.Setup
import VerifiedGarbage.Proof.X448.Arm.Step
import VerifiedGarbage.Proof.X448.Bytes
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Ed448 (RFC 8032) on ARMv7 -/

namespace VG.Artifacts.Ed448.Arm

public def artifacts : List (Artifact Arm.target) :=
  VG.Proof.Variants.Curve448Field.Arm.variants.flatMap fun (v : Proof.Variants.Curve448Field.Arm.Variant) => [
    Spec.Ed448.publicKeyApi.artifact Arm.target {
      suffix := v.suffix
      code := Impl.Ed448.Arm.Fn.publicKey v.um
      verified := Proof.Ed448.Arm.Fn.publicKey v.um },
    Spec.Ed448.signCachedApi.artifact Arm.target {
      suffix := v.suffix
      code := Impl.Ed448.Arm.Fn.signCached v.um
      verified := Proof.Ed448.Arm.Fn.signCached v.um },
    Spec.Ed448.verifyApi.artifact Arm.target {
      suffix := v.suffix
      code := Impl.Ed448.Arm.Fn.verify v.um
      verified := Proof.Ed448.Arm.Fn.verify v.um }]

spec_apis artifacts

end VG.Artifacts.Ed448.Arm
