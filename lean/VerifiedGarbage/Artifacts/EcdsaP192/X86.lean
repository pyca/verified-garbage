module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.P192.X86.Law
public import VerifiedGarbage.Proof.Ecdsa.X86.P192.Scrub
public import VerifiedGarbage.Impl.Ecdsa.P192.X86Fn
public import VerifiedGarbage.Spec.Ecdsa.Verify.P192
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
import VerifiedGarbage.Proof.Ecdsa.X86.P192.CombLit
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.P192.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit

/-! # ECDSA over P-192 (FIPS 186-5) on x86 -/

@[expose] public section

-- Deterministic ECDSA (RFC 6979) over P-192 on x86 (32-bit), with HMAC as a table
namespace VG.Artifacts.EcdsaP192.X86.Rfc6979

open VG.Proof.P192.X86 (hasLaw)
open VG.Proof.Ecdsa.Rfc6979.X86 (OK)
open VG.Proof.HmacTable.X86 (names tables fnsOf)
open VG.Proof.Ecdsa.X86.P192.Scrub (vs sign_scrubbed)

def artifacts : List Artifact :=
  if hv : OK vs ∧ "VG_P192_COMB" ∉ names vs then [
    Spec.Ecdsa.Rfc6979.Curves.p192SignApi.artifact X86.target {
      tables := [("hmac", tables vs)]
      code := Impl.Ecdsa.X86.Fn.signP192 (fnsOf vs)
      verified := sign_scrubbed hasLaw.law hv }]
  else []

end VG.Artifacts.EcdsaP192.X86.Rfc6979

namespace VG.Artifacts.EcdsaP192.X86

open VG.Proof.P192.X86 (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdsa.P192.verifyHashApi.artifact X86.target {
    code := Impl.Ecdsa.X86.Fn.verifyP192
    verified := Proof.Ecdsa.X86.P192.Scrub.verify_scrubbed hasLaw.law }] ++
  Rfc6979.artifacts

end VG.Artifacts.EcdsaP192.X86
