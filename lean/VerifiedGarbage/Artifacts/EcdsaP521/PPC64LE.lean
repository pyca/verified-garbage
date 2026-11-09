module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdsa.P521.PPC64LE
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdsa.P521
public import VerifiedGarbage.Impl.Ecdsa.Verify.P521.PPC64LE
public import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.P521.Verified
public import VerifiedGarbage.Spec.Ecdsa.Verify.P521
public import VerifiedGarbage.Impl.Ecdsa.PPC64LE.VerifyHash
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.P521.Lit
public import VerifiedGarbage.Proof.P521.PPC64LE.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.P521
public import VerifiedGarbage.Proof.HmacTable.PPC64LE.Vars
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P521.CombLit

/-! # ECDSA signatures over P-521 (FIPS 186-5 §6.4.1) on PPC64LE -/

@[expose] public section

-- Deterministic ECDSA (RFC 6979) over P-521 on PPC64LE, with HMAC as a table
namespace VG.Artifacts.EcdsaP521.PPC64LE.Rfc6979

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

end VG.Artifacts.EcdsaP521.PPC64LE.Rfc6979

namespace VG.Artifacts.EcdsaP521.PPC64LE

open VG.Proof.P521.PPC64LE (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdsa.P521.verifyHashApi.artifact PPC64LE.target {
    code := Impl.Ecdsa.PPC64LE.VerifyHash.verifyHash Spec.Ecdsa.P521.inst.curve.len true
      Impl.Ecdsa.Verify.PPC64LE.verifyP521
    stack := 112
    verified := Proof.Ecdsa.Verify.PPC64LE.P521.verifyHash_verified hasLaw.law }] ++
  Rfc6979.artifacts

end VG.Artifacts.EcdsaP521.PPC64LE
