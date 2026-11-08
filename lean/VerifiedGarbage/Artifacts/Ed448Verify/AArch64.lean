module

public import VerifiedGarbage.Proof.Ed448.AArch64.Verify.Verified
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
public import VerifiedGarbage.Proof.Ed448.AArch64.Whole.CallsCT
public import VerifiedGarbage.Proof.Ed448.ScalarWords
public import VerifiedGarbage.Proof.Ed448.VerifyEq
public import VerifiedGarbage.Proof.Framework.AArch64.RelCT
public import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
public import VerifiedGarbage.Proof.Framework.OffsetBelow
public import VerifiedGarbage.Proof.Sha3.AArch64.Call
public import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Pad
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.Variants.Keccak.AArch64

/-! # Ed448 verification on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Ed448Verify.AArch64

def artifactsFor (v : Proof.Sha3.AArch64.Permutation) : List Artifact := [
  Spec.Ed448.verifyApi.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    vendor := v.vendor
    code := Impl.Ed448.AArch64.Verify.verifyWith v.callee
    stack := 352
    verified := Proof.Ed448.AArch64.Verify.verify_verified v
      (Proof.Ed448.AArch64.Sparse.verified_eqOk Proof.Ed448.recover_ok) }]

def artifacts : List Artifact :=
  VG.Proof.Variants.Keccak.AArch64.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.Ed448Verify.AArch64
