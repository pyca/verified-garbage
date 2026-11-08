module

public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.BrainpoolP512r1
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.BrainpoolP512r1.X86.Law
public import VerifiedGarbage.Proof.Variants.Sha1.X86
public import VerifiedGarbage.Proof.Variants.Sha256.X86

/-! # Deterministic ECDSA (RFC 6979) over brainpoolP512r1 on x86 (32-bit), with HMAC as a table -/

@[expose] public section

namespace VG.Artifacts.EcdsaBrainpoolP512r1Rfc6979.X86

open VG.Proof.BrainpoolP512r1.X86 (hasLaw)
open VG.Proof.Ecdsa.Rfc6979.X86 (signCodeT stackT OK brainpoolp512r1 brainpoolp512r1T_verified signCode_sp)
open VG.Proof.HmacTable.X86 (tables names vars)

def artifactsFor (vs1 : List Proof.Sha1.X86.Variants.Backend)
    (vs256 : List Proof.Sha256.X86.Variants.Backend) : List Artifact :=
  if hv : OK (vars vs1 vs256) then [
    Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1SignApi.artifact X86.target {
      tables := [("hmac", tables (vars vs1 vs256))]
      code := signCodeT (brainpoolp512r1 hasLaw.law) Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1.tries (vars vs1 vs256)
      stack := stackT
      verified := brainpoolp512r1T_verified hasLaw.law (vars vs1 vs256) hv
      spSafe := signCode_sp _ _ _ }]
  else []

def artifacts : List Artifact :=
  artifactsFor VG.Proof.Variants.Sha1.X86.variants VG.Proof.Variants.Sha256.X86.variants

end VG.Artifacts.EcdsaBrainpoolP512r1Rfc6979.X86
