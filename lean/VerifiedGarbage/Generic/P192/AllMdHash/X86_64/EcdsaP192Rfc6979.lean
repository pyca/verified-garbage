module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvInterface
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.P192
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find

/-! # Deterministic ECDSA (RFC 6979) over P-192 on x86-64, with HMAC as a table -/

@[expose] public section

namespace VG.Generic.P192.AllMdHash.X86_64.EcdsaP192Rfc6979

open VG.Proof.Ecdsa.Rfc6979.X86_64 (signCodeT stackT OK p192 p192T_verified signCode_sp)
open VG.Proof.HmacTable.X86_64 (tables names)

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInv Spec.P192.curve)
    (vs : List Proof.Pbkdf2.Md.X86_64.MdHash) : List Artifact :=
  if hv : OK vs then [
    Spec.Ecdsa.Rfc6979.Curves.p192SignApi.artifact X86_64.target {
      suffix := ""
      tables := [("hmac", tables vs)]
      code := signCodeT (p192 h.law h.inv) Spec.Ecdsa.Rfc6979.Curves.p192.tries vs
      stack := stackT
      verified := p192T_verified h.law h.inv vs hv
      spSafe := signCode_sp _ _ _
      features := [] }]
  else []

end VG.Generic.P192.AllMdHash.X86_64.EcdsaP192Rfc6979
