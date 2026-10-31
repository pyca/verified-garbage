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
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Ed448 public-key derivation on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Ed448PublicKey.PPC64LE

def artifacts : List Artifact := [
  Spec.Ed448.publicKeyApi.artifact PPC64LE.target {
    code := Impl.Ed448.PPC64LE.Whole.publicKeyCode
    stack := 240
    verified := Proof.Ed448.PPC64LE.Whole.publicKey_framed Proof.Ed448.baseLadder2_ok }]

end VG.Artifacts.Ed448PublicKey.PPC64LE
