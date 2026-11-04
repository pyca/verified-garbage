module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.BrainpoolP384r1
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Deterministic ECDSA (RFC 6979) over brainpoolP384r1 on x86 (32-bit), with the hash function as a table -/

@[expose] public section

namespace VG.Generic.BrainpoolP384r1.AllSha1.AllSha256.X86.EcdsaBrainpoolP384r1Rfc6979

open VG.Proof.Ecdsa.Rfc6979.X86 (signCode stackT OK brainpoolp384r1 brainpoolp384r1T_verified signCode_sp)
open VG.Proof.HashTable.X86 (vars tables)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP384r1.curve) (vs1 : List Proof.Sha1.X86.Variants.Backend)
    (vs256 : List Proof.Sha256.X86.Variants.Backend) : List Artifact :=
  if hv : OK (vars vs1 vs256) then [
    Spec.Ecdsa.Rfc6979.Curves.brainpoolp384r1SignApi.artifact X86.target {
      suffix := ""
      tables := [("hash", tables (vars vs1 vs256))]
      code := signCode (brainpoolp384r1 h.law) Spec.Ecdsa.Rfc6979.Curves.brainpoolp384r1.tries (vars vs1 vs256)
      stack := stackT
      verified := brainpoolp384r1T_verified h.law (vars vs1 vs256) hv
      spSafe := signCode_sp _ _ _
      features := [] }]
  else []

end VG.Generic.BrainpoolP384r1.AllSha1.AllSha256.X86.EcdsaBrainpoolP384r1Rfc6979
