module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvInterface
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.BrainpoolP384r1
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find

/-! # Deterministic ECDSA (RFC 6979) over brainpoolP384r1 on x86-64, with the hash function as a table -/

@[expose] public section

namespace VG.Generic.BrainpoolP384r1.AllMdHash.X86_64.EcdsaBrainpoolP384r1Rfc6979

open VG.Proof.Ecdsa.Rfc6979.X86_64 (signCode stackT OK brainpoolp384r1 brainpoolp384r1T_verified signCode_sp)
open VG.Proof.HashTable.X86_64 (tables names)

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInv Spec.BrainpoolP384r1.curve)
    (vs : List Proof.Pbkdf2.Md.X86_64.MdHash) : List Artifact :=
  if hv : OK vs then [
    Spec.Ecdsa.Rfc6979.Curves.brainpoolp384r1SignApi.artifact X86_64.target {
      suffix := ""
      tables := [("hash", tables vs)]
      code := signCode (brainpoolp384r1 h.law h.inv) Spec.Ecdsa.Rfc6979.Curves.brainpoolp384r1.tries vs
      stack := stackT
      verified := brainpoolp384r1T_verified h.law h.inv vs hv
      spSafe := signCode_sp _ _ _
      features := [] }]
  else []

end VG.Generic.BrainpoolP384r1.AllMdHash.X86_64.EcdsaBrainpoolP384r1Rfc6979
