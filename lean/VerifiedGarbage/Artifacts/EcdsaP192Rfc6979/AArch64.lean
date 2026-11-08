module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.P192
public import VerifiedGarbage.TCB.AArch64.Print
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.P192.AArch64.Law
public import VerifiedGarbage.Proof.Variants.MdHash.AArch64

/-! # Deterministic ECDSA (RFC 6979) over P-192 on AArch64, with HMAC as a table -/

@[expose] public section

namespace VG.Artifacts.EcdsaP192Rfc6979.AArch64

open VG.Proof.P192.AArch64 (hasLaw)
open VG.Proof.Ecdsa.Rfc6979.AArch64 (signCodeT stackT OK p192 p192T_verified)
open VG.Proof.HmacTable.AArch64 (tables names)

def artifactsFor (vs : List Proof.Pbkdf2.Md.AArch64.MdHash) : List Artifact :=
  if hv : OK vs then [
    Spec.Ecdsa.Rfc6979.Curves.p192SignApi.artifact AArch64.target {
      suffix := ""
      tables := [("hmac", tables vs)]
      code := signCodeT (p192 hasLaw.law hasLaw.inv) Spec.Ecdsa.Rfc6979.Curves.p192.tries vs
      stack := stackT
      verified := p192T_verified hasLaw.law hasLaw.inv vs hv
      features := [] }]
  else []

def artifacts : List Artifact :=
  artifactsFor VG.Proof.Variants.MdHash.AArch64.variants

end VG.Artifacts.EcdsaP192Rfc6979.AArch64
