module

public import VerifiedGarbage.Proof.Ed25519.AArch64.DivstepSound
public import VerifiedGarbage.Proof.Ed25519.AArch64.PublicKey.Expanded
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset
public import VerifiedGarbage.Proof.Framework.Registration

/-! Ed25519 public-key derivation from the seed's SHA-512 digest. -/

@[expose] public section

namespace VG.Artifacts.Ed25519PublicKeyExpanded.AArch64

def artifacts : List Artifact := [
  Spec.Ed25519.publicKeyExpandedApi.artifact AArch64.target {
    code := Impl.Ed25519.AArch64.PublicKey.codeExpanded
    consts := Impl.Ed25519.AArch64.combConsts
    stack := 352
    verified := Proof.Ed25519.AArch64.PublicKey.publicKeyExpanded_verified }]

end VG.Artifacts.Ed25519PublicKeyExpanded.AArch64
