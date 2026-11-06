module

public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.P521
public import VerifiedGarbage.TCB.X86.Print

/-! # Deterministic ECDSA (RFC 6979) over P-521 on x86 (32-bit), with HMAC as a table -/

@[expose] public section

namespace VG.Generic.P521.AllSha1.AllSha256.X86.EcdsaP521Rfc6979

open VG.Proof.Ecdsa.Rfc6979.X86 (signCodeT stackT OK p521 p521T_verified signCode_sp)
open VG.Proof.HmacTable.X86 (tables names vars)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P521.curve) (vs1 : List Proof.Sha1.X86.Variants.Backend)
    (vs256 : List Proof.Sha256.X86.Variants.Backend) : List Artifact :=
  if hv : OK (vars vs1 vs256) then [
    Spec.Ecdsa.Rfc6979.Curves.p521SignApi.artifact X86.target {
      tables := [("hmac", tables (vars vs1 vs256))]
      code := signCodeT (p521 h.law) Spec.Ecdsa.Rfc6979.Curves.p521.tries (vars vs1 vs256)
      stack := stackT
      verified := p521T_verified h.law (vars vs1 vs256) hv
      spSafe := signCode_sp _ _ _ }]
  else []

end VG.Generic.P521.AllSha1.AllSha256.X86.EcdsaP521Rfc6979
