module

public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.P256
public import VerifiedGarbage.TCB.X86.Print

/-! # Deterministic ECDSA (RFC 6979) over P-256 on x86 (32-bit), with HMAC as a table -/

@[expose] public section

namespace VG.Generic.P256.AllSha1.AllSha256.X86.EcdsaP256Rfc6979

open VG.Proof.Ecdsa.Rfc6979.X86 (signCodeT stackT OK p256 p256T_verified signCode_sp)
open VG.Proof.HmacTable.X86 (tables names vars)

def artifacts (h : Proof.Weierstrass.X86.Inv.HasLawInvOrd Spec.P256.curve) (vs1 : List Proof.Sha1.X86.Variants.Backend)
    (vs256 : List Proof.Sha256.X86.Variants.Backend) : List Artifact :=
  if hv : OK (vars vs1 vs256) ∧ "VG_P256_COMB" ∉ names (vars vs1 vs256) then [
    Spec.Ecdsa.Rfc6979.Curves.p256SignApi.artifact X86.target {
      tables := [("hmac", tables (vars vs1 vs256))]
      code := signCodeT (p256 h.law h.inv) Spec.Ecdsa.Rfc6979.Curves.p256.tries (vars vs1 vs256)
      consts := Impl.Ecdsa.X86.p256Comb.combConsts
      stack := stackT
      verified := p256T_verified h.law h.inv (vars vs1 vs256) hv
      spSafe := signCode_sp _ _ _ }]
  else []

end VG.Generic.P256.AllSha1.AllSha256.X86.EcdsaP256Rfc6979
