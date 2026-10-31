module

public import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.SignVerified
public import VerifiedGarbage.Proof.Ed448.Facts
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Ed448 signing with a cached public key on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Ed448SignCached.PPC64LE

def artifacts : List Artifact := [
  Spec.Ed448.signCachedApi.artifact PPC64LE.target {
    code := Impl.Ed448.PPC64LE.Whole.signCachedCode
    stack := 624
    verified := Proof.Ed448.PPC64LE.Whole.signCached_framed Proof.Ed448.baseLadder2_ok }]

end VG.Artifacts.Ed448SignCached.PPC64LE
