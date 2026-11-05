module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvInterface
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Secp256k1
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find

/-! # Deterministic ECDSA (RFC 6979) over secp256k1 on x86-64, with HMAC as a table -/

@[expose] public section

namespace VG.Generic.Secp256k1.AllMdHash.X86_64.EcdsaSecp256k1Rfc6979

open VG.Proof.Ecdsa.Rfc6979.X86_64 (signCodeT stackT OK secp256k1 secp256k1T_verified signCode_sp)
open VG.Proof.HmacTable.X86_64 (tables names)

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInv Spec.Secp256k1.curve)
    (vs : List Proof.Pbkdf2.Md.X86_64.MdHash) : List Artifact :=
  if hv : OK vs then [
    Spec.Ecdsa.Rfc6979.Curves.secp256k1SignApi.artifact X86_64.target {
      suffix := ""
      tables := [("hmac", tables vs)]
      code := signCodeT (secp256k1 h.law h.inv) Spec.Ecdsa.Rfc6979.Curves.secp256k1.tries vs
      stack := stackT
      verified := secp256k1T_verified h.law h.inv vs hv
      spSafe := signCode_sp _ _ _
      features := [] }]
  else []

end VG.Generic.Secp256k1.AllMdHash.X86_64.EcdsaSecp256k1Rfc6979
