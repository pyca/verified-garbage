module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.PublicKeyVerified
import VerifiedGarbage.Proof.Ed448.Facts
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset
import VerifiedGarbage.Proof.Ed448.PPC64LE.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.SignVerified
import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.VerifyVerified
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Ed448 (RFC 8032) on PPC64LE -/

namespace VG.Artifacts.Ed448.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Ed448.publicKeyApi.artifact PPC64LE.target {
    code := Impl.Ed448.PPC64LE.Fn.publicKey
    verified := Proof.Ed448.PPC64LE.Scrub.publicKey_scrubbed },
  Spec.Ed448.signCachedApi.artifact PPC64LE.target {
    code := Impl.Ed448.PPC64LE.Fn.signCached
    verified := Proof.Ed448.PPC64LE.Scrub.signCached_scrubbed },
  Spec.Ed448.verifyApi.artifact PPC64LE.target {
    code := Impl.Ed448.PPC64LE.Fn.verify
    verified := Proof.Ed448.PPC64LE.Scrub.verify_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Ed448.PPC64LE
