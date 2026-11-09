module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.P521
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.HmacTable.PPC64LE.Vars
public import VerifiedGarbage.TCB.PPC64LE.Print
public import VerifiedGarbage.Proof.P521.PPC64LE.Law
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P521.CombLit

/-! # Deterministic ECDSA (RFC 6979) over P-521 on PPC64LE, with HMAC as a table -/

@[expose] public section

namespace VG.Artifacts.EcdsaP521Rfc6979.PPC64LE

open VG.Proof.P521.PPC64LE (hasLaw)
open VG.Proof.Ecdsa.Rfc6979.PPC64LE (signCodeT stackT OK p521R p521T_verified)
open VG.Proof.HmacTable.PPC64LE (vars tables names)

def artifacts : List Artifact :=
  if hv : OK vars ∧ "VG_P521_COMB" ∉ names vars then [
    Spec.Ecdsa.Rfc6979.Curves.p521SignApi.artifact PPC64LE.target {
      tables := [("hmac", tables vars)]
      code := signCodeT (p521R hasLaw.law) Spec.Ecdsa.Rfc6979.Curves.p521.tries vars
      stack := stackT
      verified := p521T_verified hasLaw.law vars hv }]
  else []

end VG.Artifacts.EcdsaP521Rfc6979.PPC64LE
