module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.PPC64LE
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdsa.Secp256k1
public import VerifiedGarbage.Impl.Ecdsa.Verify.Secp256k1.PPC64LE
public import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.Secp256k1.Verified
public import VerifiedGarbage.Spec.Ecdsa.Verify.Secp256k1
public import VerifiedGarbage.Impl.Ecdsa.PPC64LE.VerifyHash
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.Secp256k1.Lit
public import VerifiedGarbage.Proof.Secp256k1.PPC64LE.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Secp256k1
public import VerifiedGarbage.Proof.HmacTable.PPC64LE.Vars
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Secp256k1.CombLit

/-! # ECDSA signatures over secp256k1 (FIPS 186-5 §6.4.1) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.EcdsaSecp256k1.PPC64LE

open VG.Proof.Ecdsa.Rfc6979.PPC64LE (signCodeT stackT OK secp256k1R secp256k1T_verified)
open VG.Proof.HmacTable.PPC64LE (vars tables names)

open VG.Proof.Secp256k1.PPC64LE (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdsa.Secp256k1.verifyHashApi.artifact PPC64LE.target {
    code := Impl.Ecdsa.PPC64LE.VerifyHash.verifyHash Spec.Ecdsa.Secp256k1.inst.curve.len false
      Impl.Ecdsa.Verify.PPC64LE.verifySecp256k1
    stack := 112
    verified := Proof.Ecdsa.Verify.PPC64LE.Secp256k1.verifyHash_verified hasLaw.law }] ++
  (if hv : OK vars ∧ "VG_SECP256K1_COMB" ∉ names vars then [
    Spec.Ecdsa.Rfc6979.Curves.secp256k1SignApi.artifact PPC64LE.target {
      tables := [("hmac", tables vars)]
      code := signCodeT (secp256k1R hasLaw.law) Spec.Ecdsa.Rfc6979.Curves.secp256k1.tries vars
      stack := stackT
      verified := secp256k1T_verified hasLaw.law vars hv }]
  else [])

end VG.Artifacts.EcdsaSecp256k1.PPC64LE
