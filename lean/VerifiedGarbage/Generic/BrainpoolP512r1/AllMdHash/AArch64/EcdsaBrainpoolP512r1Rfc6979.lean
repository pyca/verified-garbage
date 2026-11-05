module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.BrainpoolP512r1
public import VerifiedGarbage.TCB.AArch64.Print
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

/-! # Deterministic ECDSA (RFC 6979) over brainpoolP512r1 on AArch64, with HMAC as a table -/

@[expose] public section

namespace VG.Generic.BrainpoolP512r1.AllMdHash.AArch64.EcdsaBrainpoolP512r1Rfc6979

open VG.Proof.Ecdsa.Rfc6979.AArch64 (signCodeT stackT OK brainpoolp512r1 brainpoolp512r1T_verified)
open VG.Proof.HmacTable.AArch64 (tables names)

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInv Spec.BrainpoolP512r1.curve)
    (vs : List Proof.Pbkdf2.Md.AArch64.MdHash) : List Artifact :=
  if hv : OK vs then [
    Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1SignApi.artifact AArch64.target {
      suffix := ""
      tables := [("hmac", tables vs)]
      code := signCodeT (brainpoolp512r1 h.law h.inv) Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1.tries vs
      stack := stackT
      verified := brainpoolp512r1T_verified h.law h.inv vs hv
      features := [] }]
  else []

end VG.Generic.BrainpoolP512r1.AllMdHash.AArch64.EcdsaBrainpoolP512r1Rfc6979
