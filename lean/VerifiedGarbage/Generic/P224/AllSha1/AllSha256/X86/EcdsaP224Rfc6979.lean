module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.P224
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Deterministic ECDSA (RFC 6979) over P-224 on x86 (32-bit), with the hash function as a table -/

@[expose] public section

namespace VG.Generic.P224.AllSha1.AllSha256.X86.EcdsaP224Rfc6979

open VG.Proof.Ecdsa.Rfc6979.X86 (signCode stackT OK p224 p224T_verified signCode_sp)
open VG.Proof.HashTable.X86 (vars tables)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P224.curve) (vs1 : List Proof.Sha1.X86.Variants.Backend)
    (vs256 : List Proof.Sha256.X86.Variants.Backend) : List Artifact :=
  if hv : OK (vars vs1 vs256) then [
    Spec.Ecdsa.Rfc6979.Curves.p224SignApi.artifact X86.target {
      suffix := ""
      tables := [("hash", tables (vars vs1 vs256))]
      code := signCode (p224 h.law) Spec.Ecdsa.Rfc6979.Curves.p224.tries (vars vs1 vs256)
      stack := stackT
      verified := p224T_verified h.law (vars vs1 vs256) hv
      spSafe := signCode_sp _ _ _
      features := [] }]
  else []

end VG.Generic.P224.AllSha1.AllSha256.X86.EcdsaP224Rfc6979
