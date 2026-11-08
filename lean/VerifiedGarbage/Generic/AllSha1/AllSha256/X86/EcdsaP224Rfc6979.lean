module

public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.P224
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.P224.X86.Law

/-! # Deterministic ECDSA (RFC 6979) over P-224 on x86 (32-bit), with HMAC as a table -/

@[expose] public section

namespace VG.Generic.AllSha1.AllSha256.X86.EcdsaP224Rfc6979

open VG.Proof.P224.X86 (hasLaw)
open VG.Proof.Ecdsa.Rfc6979.X86 (signCodeT stackT OK p224 p224T_verified signCode_sp)
open VG.Proof.HmacTable.X86 (tables names vars)

def artifacts (vs1 : List Proof.Sha1.X86.Variants.Backend)
    (vs256 : List Proof.Sha256.X86.Variants.Backend) : List Artifact :=
  if hv : OK (vars vs1 vs256) then [
    Spec.Ecdsa.Rfc6979.Curves.p224SignApi.artifact X86.target {
      tables := [("hmac", tables (vars vs1 vs256))]
      code := signCodeT (p224 hasLaw.law) Spec.Ecdsa.Rfc6979.Curves.p224.tries (vars vs1 vs256)
      stack := stackT
      verified := p224T_verified hasLaw.law (vars vs1 vs256) hv
      spSafe := signCode_sp _ _ _ }]
  else []

end VG.Generic.AllSha1.AllSha256.X86.EcdsaP224Rfc6979
