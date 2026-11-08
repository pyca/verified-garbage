module

public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.P256
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.P256.X86.Law
public import VerifiedGarbage.Proof.Variants.Sha1.X86
public import VerifiedGarbage.Proof.Variants.Sha256.X86

/-! # Deterministic ECDSA (RFC 6979) over P-256 on x86 (32-bit), with HMAC as a table -/

@[expose] public section

namespace VG.Artifacts.EcdsaP256Rfc6979.X86

open VG.Proof.P256.X86 (hasLaw)
open VG.Proof.Ecdsa.Rfc6979.X86 (signCodeT stackT OK p256 p256T_verified signCode_sp)
open VG.Proof.HmacTable.X86 (tables names vars)

def artifactsFor (vs1 : List Proof.Sha1.X86.Variants.Backend)
    (vs256 : List Proof.Sha256.X86.Variants.Backend) : List Artifact :=
  if hv : OK (vars vs1 vs256) ∧ "VG_P256_COMB" ∉ names (vars vs1 vs256) then [
    Spec.Ecdsa.Rfc6979.Curves.p256SignApi.artifact X86.target {
      tables := [("hmac", tables (vars vs1 vs256))]
      code := signCodeT (p256 hasLaw.law hasLaw.inv) Spec.Ecdsa.Rfc6979.Curves.p256.tries (vars vs1 vs256)
      stack := stackT
      verified := p256T_verified hasLaw.law hasLaw.inv (vars vs1 vs256) hv
      spSafe := signCode_sp _ _ _ }]
  else []

def artifacts : List Artifact :=
  artifactsFor VG.Proof.Variants.Sha1.X86.variants VG.Proof.Variants.Sha256.X86.variants

end VG.Artifacts.EcdsaP256Rfc6979.X86
