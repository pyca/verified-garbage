module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Secp256k1
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

/-! # Deterministic ECDSA (RFC 6979) over secp256k1 on AArch64, with the hash function as a table -/

@[expose] public section

namespace VG.Generic.Secp256k1.AllMdHash.AArch64.EcdsaSecp256k1Rfc6979

open VG.Proof.Ecdsa.Rfc6979.AArch64 (signCode stackT OK secp256k1 secp256k1T_verified)
open VG.Proof.HashTable.AArch64 (tables names)

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInv Spec.Secp256k1.curve)
    (vs : List Proof.Pbkdf2.Md.AArch64.MdHash) : List Artifact :=
  if hv : OK vs then [
    Spec.Ecdsa.Rfc6979.Curves.secp256k1SignApi.artifact AArch64.target {
      suffix := ""
      tables := [("hash", tables vs)]
      code := signCode (secp256k1 h.law h.inv) Spec.Ecdsa.Rfc6979.Curves.secp256k1.tries vs
      stack := stackT
      verified := secp256k1T_verified h.law h.inv vs hv
      features := [] }]
  else []

end VG.Generic.Secp256k1.AllMdHash.AArch64.EcdsaSecp256k1Rfc6979
