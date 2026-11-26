module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ed25519.KeyPair
public import VerifiedGarbage.Spec.Ed25519.ExpandedSign
public import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Proof.Ed25519.X86.Scrub
import VerifiedGarbage.Impl.Ed25519.X86.Fn
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Ed25519 (RFC 8032) on x86 -/

namespace VG.Artifacts.Ed25519.X86

public def artifacts : List (Artifact X86.target) := [
  Spec.Ed25519.keyPairApi.artifact X86.target {
    code := Impl.Ed25519.X86.Fn.keyPair
    verified := Proof.Ed25519.X86.Scrub.keyPair_scrubbed },
  Spec.Ed25519.signExpandedApi.artifact X86.target {
    code := Impl.Ed25519.X86.Fn.signExpanded
    verified := Proof.Ed25519.X86.Scrub.signExpanded_scrubbed },
  Spec.Ed25519.verifyApi.artifact X86.target {
    code := Impl.Ed25519.X86.Fn.verify
    verified := Proof.Ed25519.X86.Scrub.verify_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Ed25519.X86
