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

@[expose] public section

namespace VG.Artifacts.Ed25519PublicKey.X86

def artifacts : List Artifact := [
  Spec.Ed25519.publicKeyApi.artifact X86.target {
    notes := ["Includes SHA-512 of the seed, RFC 8032 pruning, \
      and base-point multiplication. The temporary seed hash and scalar are cleared before returning."]
    consts := Impl.Ed25519.X86.combConsts
    code := Impl.Ed25519.X86.PublicKey.publicKey
    stack := 280
    verified := Proof.Ed25519.X86.PublicKey.publicKey_verified }]

end VG.Artifacts.Ed25519PublicKey.X86
