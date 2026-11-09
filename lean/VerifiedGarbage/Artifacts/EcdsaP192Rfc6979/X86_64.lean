module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvInterface
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.P192
public import VerifiedGarbage.TCB.X86_64.Print
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
public import VerifiedGarbage.Proof.P192.X86_64.Law
public import VerifiedGarbage.Proof.Variants.MdHash.X86_64

/-! # Deterministic ECDSA (RFC 6979) over P-192 on x86-64, with HMAC as a table -/

@[expose] public section

namespace VG.Artifacts.EcdsaP192Rfc6979.X86_64

open VG.Proof.P192.X86_64 (hasLaw)
open VG.Proof.Ecdsa.Rfc6979.X86_64 (signCodeT stackT OK p192 p192T_verified signCode_sp)
open VG.Proof.HmacTable.X86_64 (tables names)

def artifactsFor (vs : List Proof.Pbkdf2.Md.X86_64.MdHash) : List Artifact :=
  if hv : OK vs then [
    Spec.Ecdsa.Rfc6979.Curves.p192SignApi.artifact X86_64.target {
      suffix := ""
      tables := [("hmac", tables vs)]
      code := signCodeT (p192 hasLaw.law hasLaw.inv) Spec.Ecdsa.Rfc6979.Curves.p192.tries vs
      stack := stackT
      verified := p192T_verified hasLaw.law hasLaw.inv vs hv
      spSafe := signCode_sp _ _ _
      features := [] }]
  else []

def artifacts : List Artifact :=
  artifactsFor VG.Proof.Variants.MdHash.X86_64.variants

end VG.Artifacts.EcdsaP192Rfc6979.X86_64
