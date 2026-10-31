module

public import VerifiedGarbage.Proof.Ed448.AArch64.SignCached.Verified
public import VerifiedGarbage.Proof.Ed448.AArch64.BaseVerified
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Ed448 signing with a cached public key on AArch64 -/

@[expose] public section

namespace VG.Generic.Keccak.AArch64.Ed448SignCached

def artifacts (v : Proof.Sha3.AArch64.Permutation) : List Artifact := [
  Spec.Ed448.signCachedApi.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    consts := Impl.X448.AArch64.Base.combConsts
    code := Impl.Ed448.AArch64.SignCached.signCachedWith v.callee
    stack := 352
    verified := Proof.Ed448.AArch64.SignCached.signCached_verified v Proof.Ed448.AArch64.scalarBase_baseOk }]

end VG.Generic.Keccak.AArch64.Ed448SignCached
