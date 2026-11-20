module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.P521.X86.Law
public import VerifiedGarbage.Proof.Ecdsa.X86.P521.Scrub
public import VerifiedGarbage.Spec.Ecdsa.Verify.P521
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
import VerifiedGarbage.Proof.Ecdsa.X86.P521.CombLit
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.P521.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit

/-! # ECDSA over P-521 (FIPS 186-5) on x86 -/

@[expose] public section

-- Deterministic ECDSA (RFC 6979) over P-521 on x86 (32-bit), with HMAC as a table
namespace VG.Artifacts.EcdsaP521.X86.Rfc6979

open VG.Proof.P521.X86 (hasLaw)
open VG.Proof.Ecdsa.Rfc6979.X86 (OK)
open VG.Proof.HmacTable.X86 (names)
open VG.Proof.Ecdsa.X86.P521.Scrub (vs signReg)

def artifacts : List Artifact :=
  if hv : OK vs ∧ "VG_P521_COMB" ∉ names vs then [
    Spec.Ecdsa.Rfc6979.Curves.p521SignApi.artifact X86.target (signReg hasLaw.law hv)]
  else []

end VG.Artifacts.EcdsaP521.X86.Rfc6979

namespace VG.Artifacts.EcdsaP521.X86

open VG.Proof.P521.X86 (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdsa.P521.verifyHashApi.artifact X86.target (Proof.Ecdsa.X86.P521.Scrub.verifyReg hasLaw.law)] ++
  Rfc6979.artifacts

end VG.Artifacts.EcdsaP521.X86
