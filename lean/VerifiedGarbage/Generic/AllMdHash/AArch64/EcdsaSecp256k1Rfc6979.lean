module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Secp256k1
public import VerifiedGarbage.TCB.AArch64.Print
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Secp256k1.AArch64.Law

/-! # Deterministic ECDSA (RFC 6979) over secp256k1 on AArch64, with HMAC as a table -/

@[expose] public section

namespace VG.Generic.AllMdHash.AArch64.EcdsaSecp256k1Rfc6979

open VG.Proof.Secp256k1.AArch64 (hasLaw)
open VG.Proof.Ecdsa.Rfc6979.AArch64 (signCodeT stackT OK secp256k1 secp256k1T_verified)
open VG.Proof.HmacTable.AArch64 (tables names)

def artifacts (vs : List Proof.Pbkdf2.Md.AArch64.MdHash) : List Artifact :=
  if hv : OK vs then [
    Spec.Ecdsa.Rfc6979.Curves.secp256k1SignApi.artifact AArch64.target {
      suffix := ""
      tables := [("hmac", tables vs)]
      code := signCodeT (secp256k1 hasLaw.law hasLaw.inv) Spec.Ecdsa.Rfc6979.Curves.secp256k1.tries vs
      stack := stackT
      verified := secp256k1T_verified hasLaw.law hasLaw.inv vs hv
      features := [] }]
  else []

end VG.Generic.AllMdHash.AArch64.EcdsaSecp256k1Rfc6979
