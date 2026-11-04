module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
public import VerifiedGarbage.Proof.P384.Comb7
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.P384
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

/-! # Deterministic ECDSA (RFC 6979) over P-384 on AArch64, with the hash function as a table -/

@[expose] public section

namespace VG.Generic.P384.AllMdHash.AArch64.EcdsaP384Rfc6979

open VG.Proof.Ecdsa.Rfc6979.AArch64 (signCode stackT OK p384 p384T_verified)
open VG.Proof.HashTable.AArch64 (tables names)

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInvOrd Spec.P384.curve)
    (vs : List Proof.Pbkdf2.Md.AArch64.MdHash) : List Artifact :=
  if hv : OK vs ∧ Impl.Ecdsa.AArch64.p384.tsym ∉ names vs then [
    Spec.Ecdsa.Rfc6979.Curves.p384SignApi.artifact AArch64.target {
      suffix := ""
      tables := [("hash", tables vs)]
      code := signCode (p384 h.law h.inv (Proof.P384.combOk7 h.law)) Spec.Ecdsa.Rfc6979.Curves.p384.tries vs
      consts := Impl.Ecdsa.AArch64.p384.combConsts
      stack := stackT
      verified := p384T_verified h.law h.inv (Proof.P384.combOk7 h.law) vs hv
      features := [] }]
  else []

end VG.Generic.P384.AllMdHash.AArch64.EcdsaP384Rfc6979
