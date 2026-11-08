module

public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.BrainpoolP384r1
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.BrainpoolP384r1.X86.Law

/-! # Deterministic ECDSA (RFC 6979) over brainpoolP384r1 on x86 (32-bit), with HMAC as a table -/

@[expose] public section

namespace VG.Generic.AllSha1.AllSha256.X86.EcdsaBrainpoolP384r1Rfc6979

open VG.Proof.BrainpoolP384r1.X86 (hasLaw)
open VG.Proof.Ecdsa.Rfc6979.X86 (signCodeT stackT OK brainpoolp384r1 brainpoolp384r1T_verified signCode_sp)
open VG.Proof.HmacTable.X86 (tables names vars)

def artifacts (vs1 : List Proof.Sha1.X86.Variants.Backend)
    (vs256 : List Proof.Sha256.X86.Variants.Backend) : List Artifact :=
  if hv : OK (vars vs1 vs256) then [
    Spec.Ecdsa.Rfc6979.Curves.brainpoolp384r1SignApi.artifact X86.target {
      tables := [("hmac", tables (vars vs1 vs256))]
      code := signCodeT (brainpoolp384r1 hasLaw.law) Spec.Ecdsa.Rfc6979.Curves.brainpoolp384r1.tries (vars vs1 vs256)
      stack := stackT
      verified := brainpoolp384r1T_verified hasLaw.law (vars vs1 vs256) hv
      spSafe := signCode_sp _ _ _ }]
  else []

end VG.Generic.AllSha1.AllSha256.X86.EcdsaBrainpoolP384r1Rfc6979
