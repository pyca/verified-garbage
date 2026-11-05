module

public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Secp256k1

/-! # Deterministic ECDSA (RFC 6979) over secp256k1 on x86 (32-bit), with HMAC as a table -/

@[expose] public section

namespace VG.Generic.Secp256k1.AllSha1.AllSha256.X86.EcdsaSecp256k1Rfc6979

open VG.Proof.Ecdsa.Rfc6979.X86 (signCodeT stackT OK secp256k1 secp256k1T_verified signCode_sp)
open VG.Proof.HmacTable.X86 (tables names vars)

def artifacts (h : Proof.Weierstrass.X86.Inv.HasLawInv Spec.Secp256k1.curve) (vs1 : List Proof.Sha1.X86.Variants.Backend)
    (vs256 : List Proof.Sha256.X86.Variants.Backend) : List Artifact :=
  if hv : OK (vars vs1 vs256) then [
    Spec.Ecdsa.Rfc6979.Curves.secp256k1SignApi.artifact X86.target {
      tables := [("hmac", tables (vars vs1 vs256))]
      code := signCodeT (secp256k1 h.law h.inv) Spec.Ecdsa.Rfc6979.Curves.secp256k1.tries (vars vs1 vs256)
      consts := Impl.Ecdsa.X86.secp256k1.combConsts
      stack := stackT
      verified := secp256k1T_verified h.law h.inv (vars vs1 vs256) hv
      spSafe := signCode_sp _ _ _ }]
  else []

end VG.Generic.Secp256k1.AllSha1.AllSha256.X86.EcdsaSecp256k1Rfc6979
