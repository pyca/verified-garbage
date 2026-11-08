module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Secp256k1
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.HmacTable.PPC64LE.Vars
public import VerifiedGarbage.TCB.PPC64LE.Print
public import VerifiedGarbage.Proof.Secp256k1.PPC64LE.Law

/-! # Deterministic ECDSA (RFC 6979) over secp256k1 on PPC64LE, with HMAC as a table -/

@[expose] public section

namespace VG.Artifacts.EcdsaSecp256k1Rfc6979.PPC64LE

open VG.Proof.Secp256k1.PPC64LE (hasLaw)
open VG.Proof.Ecdsa.Rfc6979.PPC64LE (signCodeT stackT OK secp256k1R secp256k1T_verified)
open VG.Proof.HmacTable.PPC64LE (vars tables)

def artifacts : List Artifact :=
  if hv : OK vars then [
    Spec.Ecdsa.Rfc6979.Curves.secp256k1SignApi.artifact PPC64LE.target {
      tables := [("hmac", tables vars)]
      code := signCodeT (secp256k1R hasLaw.law) Spec.Ecdsa.Rfc6979.Curves.secp256k1.tries vars
      stack := stackT
      verified := secp256k1T_verified hasLaw.law vars hv }]
  else []

end VG.Artifacts.EcdsaSecp256k1Rfc6979.PPC64LE
