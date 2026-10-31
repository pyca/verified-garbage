module

public import VerifiedGarbage.Proof.Ed25519.AArch64.DivstepSound
public import VerifiedGarbage.Proof.Ed25519.AArch64.SignCached.Expanded
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Variant
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Ed25519 signing from the seed's SHA-512 digest on AArch64, for each SHA-512 implementation -/

@[expose] public section

namespace VG.Generic.MdHash.AArch64.Ed25519SignExpanded

def artifacts (h : Proof.Pbkdf2.Md.AArch64.MdHash) : List Artifact :=
  match h.sha512 with
  | none => []
  | some v => [
  Spec.Ed25519.signExpandedApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.Ed25519.AArch64.SignCached.codeExpanded v.code v.suffix
    consts := Impl.Ed25519.AArch64.combConsts
    stack := 352
    verified := Proof.Ed25519.AArch64.SignCached.signExpanded_verified v
    features := v.features }]

end VG.Generic.MdHash.AArch64.Ed25519SignExpanded
