module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvInterface
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Secp256k1
public import VerifiedGarbage.TCB.X86_64.Print
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
public import VerifiedGarbage.Proof.Secp256k1.X86_64.Law

/-! # Deterministic ECDSA (RFC 6979) over secp256k1 on x86-64, with HMAC as a table -/

@[expose] public section

namespace VG.Generic.AllMdHash.X86_64.EcdsaSecp256k1Rfc6979

open VG.Proof.Secp256k1.X86_64 (hasLaw)
open VG.Proof.Ecdsa.Rfc6979.X86_64 (signCodeT stackT OK secp256k1 secp256k1T_verified signCode_sp)
open VG.Proof.HmacTable.X86_64 (tables names)

def artifacts (vs : List Proof.Pbkdf2.Md.X86_64.MdHash) : List Artifact :=
  if hv : OK vs then [
    Spec.Ecdsa.Rfc6979.Curves.secp256k1SignApi.artifact X86_64.target {
      suffix := ""
      tables := [("hmac", tables vs)]
      code := signCodeT (secp256k1 hasLaw.law hasLaw.inv) Spec.Ecdsa.Rfc6979.Curves.secp256k1.tries vs
      stack := stackT
      verified := secp256k1T_verified hasLaw.law hasLaw.inv vs hv
      spSafe := signCode_sp _ _ _
      features := [] }]
  else []

end VG.Generic.AllMdHash.X86_64.EcdsaSecp256k1Rfc6979
