module

public import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.PublicKeyVerified
public import VerifiedGarbage.Proof.Ed448.Facts
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset
public import VerifiedGarbage.Proof.Ed448.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print
public import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.SignVerified
public import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.VerifyVerified

/-! # Ed448 (RFC 8032) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Ed448.PPC64LE

def artifacts : List Artifact := [
  Spec.Ed448.publicKeyApi.artifact PPC64LE.target Proof.Ed448.PPC64LE.Scrub.publicKeyReg,
  Spec.Ed448.signCachedApi.artifact PPC64LE.target Proof.Ed448.PPC64LE.Scrub.signCachedReg,
  Spec.Ed448.verifyApi.artifact PPC64LE.target Proof.Ed448.PPC64LE.Scrub.verifyReg]

end VG.Artifacts.Ed448.PPC64LE
