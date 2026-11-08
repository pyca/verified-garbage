module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.P224
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.HmacTable.PPC64LE.Vars
public import VerifiedGarbage.TCB.PPC64LE.Print
public import VerifiedGarbage.Proof.P224.PPC64LE.Law
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P224.CombLit

/-! # Deterministic ECDSA (RFC 6979) over P-224 on PPC64LE, with HMAC as a table -/

@[expose] public section

namespace VG.Artifacts.EcdsaP224Rfc6979.PPC64LE

open VG.Proof.P224.PPC64LE (hasLaw)
open VG.Proof.Ecdsa.Rfc6979.PPC64LE (signCodeT stackT OK p224R p224T_verified)
open VG.Proof.HmacTable.PPC64LE (vars tables names)

def artifacts : List Artifact :=
  if hv : OK vars ∧ "VG_P224_COMB" ∉ names vars then [
    Spec.Ecdsa.Rfc6979.Curves.p224SignApi.artifact PPC64LE.target {
      tables := [("hmac", tables vars)]
      code := signCodeT (p224R hasLaw.law) Spec.Ecdsa.Rfc6979.Curves.p224.tries vars
      stack := stackT
      verified := p224T_verified hasLaw.law vars hv }]
  else []

end VG.Artifacts.EcdsaP224Rfc6979.PPC64LE
