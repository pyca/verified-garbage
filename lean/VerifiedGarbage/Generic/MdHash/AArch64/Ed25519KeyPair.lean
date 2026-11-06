module

public import VerifiedGarbage.Proof.Ed25519.AArch64.DivstepSound
public import VerifiedGarbage.Proof.Ed25519.AArch64.KeyPair
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Variant
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print

/-! # Ed25519 key-pair derivation from the seed on AArch64, for each SHA-512 implementation -/

@[expose] public section

namespace VG.Generic.MdHash.AArch64.Ed25519KeyPair

/-- Key-pair derivation with the one-shot SHA-512 digest of `h`'s compression function,
calling `vg_ed25519_public_key_expanded`. -/
def artifacts (h : Proof.Pbkdf2.Md.AArch64.MdHash) : List Artifact :=
  match h.sha512 with
  | none => []
  | some v => [
  Spec.Ed25519.keyPairApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.Ed25519.AArch64.KeyPair.keyPair (Spec.Sha512.digest512Api.name ++ v.suffix)
      (Proof.Ed25519.AArch64.KeyPair.dgCode v) Spec.Ed25519.publicKeyExpandedApi.name
      Impl.Ed25519.AArch64.PublicKey.codeExpanded
    consts := Impl.Ed25519.AArch64.combConsts
    stack := 944
    verified := Proof.Ed25519.AArch64.KeyPair.verified v
    features := v.features }]

end VG.Generic.MdHash.AArch64.Ed25519KeyPair
