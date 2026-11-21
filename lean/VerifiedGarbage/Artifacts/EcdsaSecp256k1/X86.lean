module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Secp256k1.X86.Law
public import VerifiedGarbage.Proof.Ecdsa.X86.Secp256k1.Scrub
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.X86Fn
public import VerifiedGarbage.Spec.Ecdsa.Verify.Secp256k1
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
import VerifiedGarbage.Proof.Ecdsa.X86.Secp256k1.CombLit
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.Secp256k1.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit

/-! # ECDSA over secp256k1 (FIPS 186-5) on x86 -/

@[expose] public section

-- Deterministic ECDSA (RFC 6979) over secp256k1 on x86 (32-bit), with HMAC as a table
namespace VG.Artifacts.EcdsaSecp256k1.X86.Rfc6979

open VG.Proof.Secp256k1.X86 (hasLaw)
open VG.Proof.Ecdsa.Rfc6979.X86 (OK)
open VG.Proof.HmacTable.X86 (names tables fnsOf)
open VG.Proof.Ecdsa.X86.Secp256k1.Scrub (vs sign_scrubbed)

def artifacts : List Artifact :=
  if hv : OK vs ∧ "VG_SECP256K1_COMB" ∉ names vs then [
    Spec.Ecdsa.Rfc6979.Curves.secp256k1SignApi.artifact X86.target {
      tables := [("hmac", tables vs)]
      code := Impl.Ecdsa.X86.Fn.signSecp256k1 (fnsOf vs)
      verified := Proof.Ecdsa.X86.Secp256k1.Scrub.sign_scrubbed hasLaw.law hasLaw.inv hv }]
  else []

end VG.Artifacts.EcdsaSecp256k1.X86.Rfc6979

namespace VG.Artifacts.EcdsaSecp256k1.X86

open VG.Proof.Secp256k1.X86 (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdsa.Secp256k1.verifyHashApi.artifact X86.target {
    code := Impl.Ecdsa.X86.Fn.verifySecp256k1
    verified := Proof.Ecdsa.X86.Secp256k1.Scrub.verify_scrubbed hasLaw.law hasLaw.inv }] ++
  Rfc6979.artifacts

end VG.Artifacts.EcdsaSecp256k1.X86
