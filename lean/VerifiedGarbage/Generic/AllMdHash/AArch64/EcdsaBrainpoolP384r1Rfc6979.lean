module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.BrainpoolP384r1
public import VerifiedGarbage.TCB.AArch64.Print
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.BrainpoolP384r1.AArch64.Law

/-! # Deterministic ECDSA (RFC 6979) over brainpoolP384r1 on AArch64, with HMAC as a table -/

@[expose] public section

namespace VG.Generic.AllMdHash.AArch64.EcdsaBrainpoolP384r1Rfc6979

open VG.Proof.BrainpoolP384r1.AArch64 (hasLaw)
open VG.Proof.Ecdsa.Rfc6979.AArch64 (signCodeT stackT OK brainpoolp384r1 brainpoolp384r1T_verified)
open VG.Proof.HmacTable.AArch64 (tables names)

def artifacts (vs : List Proof.Pbkdf2.Md.AArch64.MdHash) : List Artifact :=
  if hv : OK vs ∧ "VG_BRAINPOOLP384R1_COMB7" ∉ names vs then [
    Spec.Ecdsa.Rfc6979.Curves.brainpoolp384r1SignApi.artifact AArch64.target {
      suffix := ""
      tables := [("hmac", tables vs)]
      code := signCodeT (brainpoolp384r1 hasLaw.law hasLaw.inv) Spec.Ecdsa.Rfc6979.Curves.brainpoolp384r1.tries vs
      stack := stackT
      verified := brainpoolp384r1T_verified hasLaw.law hasLaw.inv vs hv
      features := [] }]
  else []

end VG.Generic.AllMdHash.AArch64.EcdsaBrainpoolP384r1Rfc6979
