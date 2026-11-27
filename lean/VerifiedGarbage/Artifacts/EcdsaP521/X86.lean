module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ecdsa.Verify.P521
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.P521.X86.Law
import VerifiedGarbage.Proof.Ecdsa.X86.P521.Scrub
import VerifiedGarbage.Impl.Ecdsa.P521.X86Fn
import VerifiedGarbage.Proof.Ecdsa.X86.P521.CombLit
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.P521.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ECDSA over P-521 (FIPS 186-5) on x86 -/

-- Deterministic ECDSA (RFC 6979) over P-521 on x86 (32-bit), with HMAC as a table
namespace VG.Artifacts.EcdsaP521.X86.Rfc6979

open VG.Proof.P521.X86 (hasLaw)
open VG.Proof.Ecdsa.Rfc6979.X86 (OK)
open VG.Proof.HmacTable.X86 (names tables fnsOf)
open VG.Proof.Ecdsa.X86.P521.Scrub (vs sign_scrubbed)

def artifacts : List (Artifact X86.target) :=
  if hv : OK vs ∧ "VG_P521_COMB" ∉ names vs then [
    Spec.Ecdsa.Rfc6979.Curves.p521SignApi.artifact X86.target {
      tables := [("hmac", tables vs)]
      code := Impl.Ecdsa.X86.Fn.signP521 (fnsOf vs)
      verified := Proof.Ecdsa.X86.P521.Scrub.sign_scrubbed hasLaw.law hv }]
  else []

end VG.Artifacts.EcdsaP521.X86.Rfc6979

namespace VG.Artifacts.EcdsaP521.X86

open VG.Proof.P521.X86 (hasLaw)

public def artifacts : List (Artifact X86.target) := [
  Spec.Ecdsa.P521.verifyHashApi.artifact X86.target {
    code := Impl.Ecdsa.X86.Fn.verifyP521
    verified := Proof.Ecdsa.X86.P521.Scrub.verify_scrubbed hasLaw.law }] ++
  Rfc6979.artifacts

spec_apis artifacts

end VG.Artifacts.EcdsaP521.X86
