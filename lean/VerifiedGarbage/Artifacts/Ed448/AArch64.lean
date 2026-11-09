module

public import VerifiedGarbage.Proof.Ed448.AArch64.PublicKey.Verified
public import VerifiedGarbage.Proof.Ed448.AArch64.BaseVerified
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.Variants.Keccak.AArch64
public import VerifiedGarbage.Proof.Ed448.AArch64.SignCached.Verified
public import VerifiedGarbage.Proof.Ed448.AArch64.Verify.Verified
public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Verified
public import VerifiedGarbage.Proof.Ed448.Facts
public import VerifiedGarbage.Proof.Ed448.AArch64.CombSum
public import VerifiedGarbage.Proof.Ed448.AArch64.Point56.Lit
public import Mathlib.FieldTheory.Finite.Basic
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

/-! # Ed448 (RFC 8032) on AArch64 -/

@[expose] public section

-- Ed448 public-key derivation on AArch64
namespace VG.Artifacts.Ed448.AArch64.PublicKey

def artifactsFor (v : Proof.Sha3.AArch64.Permutation) : List Artifact := [
  Spec.Ed448.publicKeyApi.artifact AArch64.target {
    suffix := v.callee.suffix
    vendor := v.vendor
    code := Impl.Ed448.AArch64.PublicKey.publicKeyWith v.callee
    stack := 352
    verified := Proof.Ed448.AArch64.PublicKey.publicKey_verified v Proof.Ed448.AArch64.scalarBase_baseOk }]

def artifacts : List Artifact :=
  VG.Proof.Variants.Keccak.AArch64.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.Ed448.AArch64.PublicKey

-- Ed448 signing with a cached public key on AArch64
namespace VG.Artifacts.Ed448.AArch64.SignCached

def artifactsFor (v : Proof.Sha3.AArch64.Permutation) : List Artifact := [
  Spec.Ed448.signCachedApi.artifact AArch64.target {
    suffix := v.callee.suffix
    vendor := v.vendor
    code := Impl.Ed448.AArch64.SignCached.signCachedWith v.callee
    stack := 352
    verified := Proof.Ed448.AArch64.SignCached.signCached_verified v Proof.Ed448.AArch64.scalarBase_baseOk }]

def artifacts : List Artifact :=
  VG.Proof.Variants.Keccak.AArch64.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.Ed448.AArch64.SignCached

-- Ed448 verification on AArch64
namespace VG.Artifacts.Ed448.AArch64.Verify

def artifactsFor (v : Proof.Sha3.AArch64.Permutation) : List Artifact := [
  Spec.Ed448.verifyApi.artifact AArch64.target {
    suffix := v.callee.suffix
    vendor := v.vendor
    code := Impl.Ed448.AArch64.Verify.verifyWith v.callee
    stack := 352
    verified := Proof.Ed448.AArch64.Verify.verify_verified v
      (Proof.Ed448.AArch64.Sparse.verified_eqOk Proof.Ed448.recover_ok) }]

def artifacts : List Artifact :=
  VG.Proof.Variants.Keccak.AArch64.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.Ed448.AArch64.Verify

namespace VG.Artifacts.Ed448.AArch64

def artifacts : List Artifact :=
  PublicKey.artifacts ++
  SignCached.artifacts ++
  Verify.artifacts

end VG.Artifacts.Ed448.AArch64
