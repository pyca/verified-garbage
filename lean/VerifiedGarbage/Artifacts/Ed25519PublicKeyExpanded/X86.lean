module

public import VerifiedGarbage.Proof.Ed25519.X86.PublicKey.Verified
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print

/-! # Ed25519 public-key derivation from the seed's SHA-512 digest on x86 -/

@[expose] public section

namespace VG.Artifacts.Ed25519PublicKeyExpanded.X86

def artifacts : List Artifact := [
  Spec.Ed25519.publicKeyExpandedApi.artifact X86.target {
    consts := Impl.Ed25519.X86.combConsts
    code := Impl.Ed25519.X86.PublicKey.publicKeyExpanded
    stack := 280
    verified := Proof.Ed25519.X86.PublicKey.publicKeyExpanded_verified }]

end VG.Artifacts.Ed25519PublicKeyExpanded.X86
