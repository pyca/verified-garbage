module

public import VerifiedGarbage.Proof.Ed25519.X86.Scrub
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print

/-! # Ed25519 (RFC 8032) on x86 -/

@[expose] public section

namespace VG.Artifacts.Ed25519.X86

def artifacts : List Artifact := [
  Spec.Ed25519.keyPairApi.artifact X86.target Proof.Ed25519.X86.Scrub.keyPairReg,
  Spec.Ed25519.signExpandedApi.artifact X86.target Proof.Ed25519.X86.Scrub.signExpandedReg,
  Spec.Ed25519.verifyApi.artifact X86.target Proof.Ed25519.X86.Scrub.verifyReg]

end VG.Artifacts.Ed25519.X86
